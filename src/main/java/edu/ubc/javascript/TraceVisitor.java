package edu.ubc.javascript;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.google.common.base.Supplier;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public class TraceVisitor implements Callback {
	private String funcNamePrefix = "JSCompiler_func_";
	private final Supplier<String> safeNameIdSupplier;
	private final ReflectiveNodeTransformer tx;

	public TraceVisitor(Compiler c, ReflectiveNodeTransformer tx) {
		safeNameIdSupplier = c.getUniqueNameIdSupplier();
		this.tx = tx;
	}
	
	@Override
	public boolean shouldTraverse(NodeTraversal nodeTraversal, Node n, Node parent) {
		return true;
	}
			

	private Node get(Node[] scope) {
		Node call = new Node(Token.CALL);
		call.addChildToFront(Node.newString(Token.NAME, "_getTrace"));
		call.addChildrenToBack(scope[0]);
		call.addChildrenToBack(scope[1]);
		return call;
	}	
	private Node[] scope(Node n, Node parent) {
		Node ret[] = new Node[2];
		int ntype = n.getType();
		switch (ntype) {
		case Token.GETELEM:
		case Token.GETPROP:
			ret[0] = n.getFirstChild().cloneNode();
			ret[1] = n.getLastChild().cloneNode();
			return ret;
		case Token.NAME:			
			Scope s = Scope.getScope(n);
			if (s instanceof Scope.Global) {
				ret[0] = Node.newString(Token.NAME, "__global");	
			}							
			else if (parent.getType() == Token.VAR || (s instanceof Scope.Local)) {
				int ftypes[] = {Token.FUNCTION};
				Node func = NodeUti1.detectAncestor(n, ftypes);
				if (func == null) {
				    ret[0] = Node.newString(Token.NAME, "__global");
				}
				else {					
					ret[0] = Node.newString(Token.NAME, getFunctionName(func));
				}
			}
			else if (s instanceof Scope.Closed) {
				Iterator<Node> itr = n.getAncestors().iterator();				
				ArrayList<Node> ancestors = new ArrayList<Node>();
				while(itr.hasNext()) {
					Node func = itr.next();
					if (func.getType() == Token.FUNCTION) {
						ancestors.add(func);
					}
				}
				ret[0] = Node.newString(Token.NAME, getFunctionName(ancestors.get( ((Scope.Closed) s).level) ));		
			}									
			ret[1] = Node.newString(n.getString());
			return ret;
		}
		return ret;
	}
	private Node rhs(Node right, Node n) {
		if (right == null) {
			return Node.newNumber(n.getLineno());
		}
		Node ret = null;
		int rtype = right.getType();
		if (rtype == Token.GETELEM || rtype == Token.GETPROP || rtype==Token.NAME) {
			ret = get(scope(right, n));
		}
		else if (rtype == Token.CALL) {
			ret = new Node(Token.CALL);
			ret.addChildToFront(Node.newString(Token.NAME, "_popArgs"));
		}
		else if (rtype == Token.OBJECTLIT || rtype == Token.ARRAYLIT) {
			ret = Node.newNumber(right.getLineno());
		}
		else if (NodeUti1.isSimpleOperatorType(rtype)) {
			ret = new Node(Token.CALL);
			ret.addChildToFront(Node.newString(Token.NAME, "_joinTrace"));
			ret.addChildrenToBack(rhs(right.getFirstChild(), right));
			ret.addChildrenToBack(Node.newString(Token.name(rtype)));
			ret.addChildrenToBack(rhs(right.getLastChild(), right));
		}
		else {
			ret = Node.newNumber(n.getLineno());
		}
		return ret;
	}
		
	private void visitLIT(NodeTraversal t, Node n, Node parent) {
		int ntype = n.getType();
		Node cloned = n.cloneTree();
		Node traces = new Node(ntype);
		Iterator<Node> itr = cloned.children().iterator();		
		if (ntype == Token.OBJECTLIT) {			
			while (itr.hasNext()) {
				traces.addChildrenToBack(itr.next().cloneNode());
				traces.addChildrenToBack(rhs(itr.next(), cloned));
			}
		}
		else {
			while (itr.hasNext()) {
				traces.addChildrenToBack(rhs(itr.next(), cloned));
			}		
		}

		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_trace"+Token.name(ntype)));
		call.addChildrenToBack(Node.newString(NodeUti1.filename.get()));
		call.addChildrenToBack(Node.newNumber(n.getLineno()));					
		call.addChildrenToBack(cloned);			
		call.addChildrenToBack(traces);		
		tx.replace(n, call, cloned);

	}

	private void _pushArgs(Node n, String fname, Iterator<Node> itr) {
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_pushArgs"));
		call.addChildrenToBack(Node.newString(Token.name(n.getType())));
		call.addChildrenToBack(Node.newString(fname));
		while(itr.hasNext()) {
			call.addChildrenToBack(rhs(itr.next(), n));
		}
		Node before[] = {call};
		tx.insert(n, before, null);	
	}
	private void visitReturn(NodeTraversal t, Node n, Node parent) {
		String fname = "";
		int ftypes[] = {Token.FUNCTION};
		Node ancestor = NodeUti1.detectAncestor(n, ftypes);		
		if (ancestor != null) {
			fname = getFunctionName(ancestor);
		}
		_pushArgs(n, fname, n.children().iterator());
	}	
	private void visitCall(NodeTraversal t, Node n, Node parent) {
		Iterator<Node> itr = n.children().iterator();
		_pushArgs(n, itr.next().getString(), itr);
	}

	// _setTrace(url, line, value, scope, name, trace);
	private Node trace(Node value, Node[] scope, Node rhs) {
		Node call = new Node(Token.CALL);
		call.addChildToFront(Node.newString(Token.NAME, "_setTrace"));
		call.addChildrenToBack(Node.newString(NodeUti1.filename.get()));
		call.addChildrenToBack(Node.newNumber(value.getLineno()));
		call.addChildrenToBack(value.cloneTree());
		call.addChildrenToBack(scope[0]);
		call.addChildrenToBack(scope[1]);
		call.addChildrenToBack(rhs);		
		return call;
	}	
	private void visitAssign(NodeTraversal t, Node n, Node parent) {
		Node left = n.getFirstChild(), scope[] = scope(left, n), right = null;
						
		int ntype = n.getType();
		if (ntype == Token.ASSIGN) {
			right = n.getLastChild(); 
		}
		else if (ntype == Token.VAR) {
			right = left.getFirstChild();
			left = left.cloneNode();
		}	

		Node after[] = {trace(left, scope, rhs(right, n))};
		tx.insert(n, null, after);
	}
		
	Map<Node, Node> visited = new HashMap<Node, Node>();
	private String getFunctionName(Node n) {
		Node name = n.getFirstChild();
		String fname = name.getString();		
		boolean cond = true;
		
		if (fname.length() == 0) {
			fname = funcNamePrefix+ safeNameIdSupplier.get();
			name.setString(fname);				
		}
		else if (visited.containsKey(n)) {
			cond = false;
		}
		
		if (cond) {
			String tname = fname+"_trace";
			Node var = new Node(Token.VAR);
			Node vname = Node.newString(Token.NAME, tname);
			var.addChildrenToFront(vname);
			visited.put(n, var);
			
			// _traceCall(url, line, tname, args, lp);
			Node call = new Node(Token.CALL);
			vname.addChildrenToFront(call);
			call.addChildrenToFront(Node.newString(Token.NAME, "_traceCall"));
			call.addChildrenToBack(Node.newString(NodeUti1.filename.get()));
			call.addChildrenToBack(Node.newNumber(n.getLineno()));
			call.addChildrenToBack(Node.newString(tname));
			call.addChildrenToBack(Node.newString(Token.NAME, "arguments"));
						
			Node ary = new Node(Token.ARRAYLIT);
			call.addChildrenToBack(ary);
			Node lp = n.getChildAtIndex(1);
			Iterator<Node> itr = lp.children().iterator();
			while (itr.hasNext()) {
				ary.addChildrenToBack(itr.next().cloneTree());
			}			
			Node before[] = {var};

			tx.insert(n.getChildAtIndex(2).getFirstChild(), before, null);		
		}
		return fname;
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {		
		int ntype = n.getType();
		if (ntype == Token.ASSIGN || ntype == Token.VAR) {
			visitAssign(t, n, parent);
		}
		else if (ntype == Token.CALL) {
			visitCall(t, n, parent);
		}
		else if (ntype == Token.RETURN) {
			visitReturn(t, n, parent);
		}
		else if (ntype==Token.OBJECTLIT || ntype==Token.ARRAYLIT) {
			visitLIT(t, n, parent);
		}
	}
}
