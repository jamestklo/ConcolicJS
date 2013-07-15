package edu.ubc.javascript;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.google.common.base.Supplier;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public class TraceCondVisitor implements Callback {

	private final Supplier<String> safeNameIdSupplier;
	private final ReflectiveNodeTransformer tx;
	public TraceCondVisitor(Compiler c, ReflectiveNodeTransformer tx) {
		safeNameIdSupplier = c.getUniqueNameIdSupplier();
		this.tx = tx;
	}
	
	@Override
	public boolean shouldTraverse(NodeTraversal nodeTraversal, Node n, Node parent) {
		return true;
	}

	private void visitCond(NodeTraversal t, Node n, Node parent) {
		String num = safeNameIdSupplier.get();		
		Node comma = new Node(Token.COMMA);
		Node cloned = n.cloneTree();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, n);
		tx.replace(n, comma, orgs);
		
		String nodeType = Token.name(parent.getType()) +"_"+ Token.name(n.getType());
		Node enterCond = genCall("__condEnter", nodeType, num);
		comma.addChildrenToFront(enterCond);
		enterCond.addChildrenToBack(Node.newString(Token.name(n.getType())));
		enterCond.addChildrenToBack(Node.newString(Token.name(parent.getType())));
		
		Node exitCond = genCall("__condExit", nodeType, num); 			
		comma.addChildrenToBack(exitCond);
		exitCond.addChildrenToBack(cloned);		
	}

	private Map<Node, String> nodeNums = new HashMap<Node, String>();
	private String getNodeNum(Node n) {
		if (nodeNums.containsKey(n)) {
			return nodeNums.get(n);
		}
		String num = safeNameIdSupplier.get();
		nodeNums.put(n, num);
		if (n.getType()==Token.FUNCTION) {
			Node name = n.getFirstChild();
			if (name.getString().length() < 1) {
				name.setString(getFuncName(num));
			}
		}
		return num;
	}
	
	// problem: html file can have multiple <script> tags
	// goal: unique label for each logged AST node
	private static String getLabel(String nodeType, String num) {
		int scriptCount = NodeUti1.scriptCount.get();
		return nodeType +" "+ NodeUti1.filename.get() + ((scriptCount>0)?"_"+scriptCount:"") + " "+ num;
	}
	
	private static String getFuncName(String num) {
		if (num==null) {
			return null;
		}
		return "JSCompiler_func_"+ num;
	}
	
	private static Node genCall(String name, String nodeType, String num) {
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, name));
		call.addChildrenToBack(Node.newString(getLabel(nodeType, num)));
		return call;
	}
	
	private void visitFunc(NodeTraversal t, Node n, Node parent) {
		Node block = n.getChildAtIndex(2);
		Node target = block.getFirstChild();
		if (target==null) {
			return;
		}

		String num = getNodeNum(n);
		String funcname = n.getFirstChild().getString();		
		String nodeType = Token.name(n.getType());
		
		Node varFunc	= new Node(Token.VAR);
		Node nameFunc 	= Node.newString(Token.NAME, getFuncName(num)+"_c");
		varFunc.addChildrenToFront(nameFunc);		
		Node enterFunc = genCall("__funcEnter", nodeType, num);
		nameFunc.addChildrenToFront(enterFunc);
		enterFunc.addChildrenToBack(Node.newString(funcname));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "this"));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "arguments"));
		Node array = new Node(Token.ARRAYLIT);
		enterFunc.addChildrenToBack(array);
		Iterator<Node> itr = n.getChildAtIndex(1).children().iterator();
		while (itr.hasNext()) {
			array.addChildrenToBack(Node.newString(itr.next().getString()));
		}
		enterFunc.addChildrenToBack(getRootName(t));
		Node before[] = {varFunc};
		tx.insert(target, before, null);

		Node blck = new Node(Token.BLOCK);
		Node tryc = new Node(Token.TRY);
		blck.addChildrenToFront(tryc);
		Node cloned = block.cloneTree();
		tryc.addChildrenToFront(cloned);
		
		String exceptionName = getFuncName(num) +"_e";
		Node catb = new Node(Token.BLOCK);
		tryc.addChildrenToBack(catb);
		Node catc = new Node(Token.CATCH);
		catb.addChildrenToFront(catc);
		catc.addChildrenToFront(Node.newString(Token.NAME, exceptionName));
		catb = new Node(Token.BLOCK);
		catc.addChildrenToBack(catb);
		
		Node exitExpr = new Node(Token.EXPR_RESULT);
		catb.addChildrenToBack(exitExpr);
		Node exitFunc = genCall("__funcExit", nodeType, num);
		exitExpr.addChildrenToFront(exitFunc);
		Node exitFun2 = exitFunc.cloneTree();
		exitFunc.addChildrenToBack(Node.newString(Token.NAME, exceptionName));
		
		Node thrw = new Node(Token.THROW);
		catb.addChildrenToBack(thrw);
		thrw.addChildrenToFront(Node.newString(Token.NAME, exceptionName));
		
		blck.addChildrenToBack(exitFun2); // exception not thrown here
		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, block);
		tx.replace(block, blck, orgs);
		
		Node assign = new Node(Token.ASSIGN);
		Node getElem = new Node(Token.GETELEM);
		assign.addChildrenToFront(getElem);
		getElem.addChildrenToFront(Node.newString(Token.NAME, "__astGlobal"));
		getElem.addChildrenToBack(Node.newString(getLabel(nodeType, num)));		
		if (NodeUti1.isStatement(n)) {
			assign.addChildrenToBack(Node.newString(Token.NAME, funcname));
			Node after[] = {assign};
			tx.insert(n, null, after);
		}
		else {
			Node n2 = n.cloneTree();
			assign.addChildrenToBack(n2);
			Map<Node, Node> orgs2 = new HashMap<Node, Node>();			
			orgs2.put(n2, n);
			tx.replace(n, assign, orgs2);
		}		
	}
		
	private Node getRootName(NodeTraversal t) {
		Node root = t.getScopeRoot();
		if (root.getType()==Token.FUNCTION) {
			return Node.newString(Token.NAME, getFuncName(getNodeNum(root)));
		}
		else {
			return new Node(Token.NULL);
		}		
	}	
		
	private void visitReturn(NodeTraversal t, Node n, Node parent) {
		Node target = n.getFirstChild();
		if (target == null) {
			target = Node.newString(Token.NAME, "undefined");
			n.addChildrenToFront(target);
		}
		Node func = t.getScopeRoot();
		if (func.getType()==Token.FUNCTION) {
			Node cloned = target.cloneTree();
			Node exitFunc = genCall("__funcExit", Token.name(func.getType()), getNodeNum(func));
			exitFunc.addChildrenToBack(cloned);
			Map<Node, Node> orgs = new HashMap<Node, Node>();
			orgs.put(cloned, target);
			tx.replace(target, exitFunc, orgs);
		}
	}
	
	private void visitCall(NodeTraversal t, Node n, Node parent) {
		Node cloned = n.cloneTree();
		Node fname = cloned.getFirstChild();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		switch (fname.getType()) {
		case Token.GETELEM:
		case Token.GETPROP:
			cloned.addChildrenToFront(Node.newString(Token.NAME, "_CALLGET"));						
			Node target = fname.removeFirstChild();
			Node key = fname.removeFirstChild();
			cloned.addChildBefore(target, fname);
			cloned.addChildBefore(key, fname);
			cloned.removeChild(fname);						
			Node name = n.getFirstChild();
			orgs.put(target, name.getFirstChild());
			orgs.put(key, name.getLastChild());									
			break;
		case Token.NAME: 
			cloned.addChildrenToFront(Node.newString(Token.NAME, "_CALL"));
			break;
		}
		tx.replace(n, cloned, orgs);
	}
	
	private void visitSet(NodeTraversal t, Node n, Node parent) {		
		Node target = n.getFirstChild();		
		Node key	= n.getLastChild();
		Node right = parent.getLastChild();		

		Node target_clone = target.cloneTree();
		Node key_clone = key.cloneTree();
		Node right_clone = right.cloneTree();
		
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_SET"));
		call.addChildrenToBack(target_clone);
		call.addChildrenToBack(key_clone);
		call.addChildrenToBack(right_clone);
		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(target_clone, target);
		orgs.put(key_clone, key);
		orgs.put(right_clone, right);
		tx.replace(parent, call, orgs);
	}
	
	private void visitGet(NodeTraversal t, Node n, Node parent) {
		int ptype = parent.getType();
		if (ptype==Token.CALL) {
			return;			
		}
				
		Node target = n.getFirstChild();
		Node target_cloned = target.cloneTree();
				
		Node key = n.getLastChild();
		Node key_cloned = key.cloneTree();
				
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_GET"));
		call.addChildrenToBack(target_cloned);
		call.addChildrenToBack(key_cloned);
		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(target_cloned, target);
		orgs.put(key_cloned, key);
		tx.replace(n, call, orgs);
	}
	
	private void visitConst(NodeTraversal t, Node n, Node parent) {
		Node cloned = n.cloneTree();
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_CONST"));
		call.addChildrenToBack(Node.newString(getLabel(Token.name(n.getType()), safeNameIdSupplier.get())));
		call.addChildrenToBack(cloned);
		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, n);
		tx.replace(n,  call, orgs);		
	}
	
	private void visitProto(NodeTraversal t, Node n, Node parent) {
		Node child = n.getFirstChild();
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_PROTO"));
		Node cloned = child.cloneTree();
		call.addChildrenToBack(cloned);		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, child);
		tx.replace(child, call, orgs);
	}
	private void visitOps(NodeTraversal t, Node n, Node parent) {
		Node n1 = n.getFirstChild();
		Node n2 = n.getLastChild();		
		Node c1 = n1.cloneTree();
		Node c2 = n2.cloneTree();
		
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(n.getType())));
		call.addChildrenToBack(c1);
		call.addChildrenToBack(c2);
		/*
		Node func = new Node(Token.FUNCTION);
		call.addChildrenToBack(func);
		func.addChildrenToFront(Node.newString(Token.NAME, Token.name(n.getType())));
		Node para = new Node(Token.PARAM_LIST);
		func.addChildrenToBack(para);
		para.addChildrenToFront(Node.newString(Token.NAME, "left"));
		para.addChildrenToBack(Node.newString(Token.NAME, "right"));
		Node blck = new Node(Token.BLOCK);
		func.addChildrenToBack(blck);
		Node expr = new Node(Token.EXPR_RESULT);
		blck.addChildrenToBack(expr);
		Node retn = new Node(Token.RETURN);
		expr.addChildrenToFront(retn);
		Node opsc = new Node(n.getType());
		retn.addChildrenToFront(opsc);
		opsc.addChildrenToFront(Node.newString(Token.NAME, "left"));
		opsc.addChildrenToBack(Node.newString(Token.NAME, "right"));
		*/	
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(c1, n1);
		orgs.put(c2, n2);
		tx.replace(n, call, orgs);
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
		int ntype = n.getType();
		int ptype = (parent == null)?Token.NULL:parent.getType();
		
		if (ntype == Token.EMPTY) {
			return;
		}
		else if (ntype==Token.NEW && n.getFirstChild().getNext()==null) {
			n.addChildrenToBack(new Node(Token.EMPTY));
		}
		else if (ntype==Token.STRING_KEY && n.getString().equals("__proto__")) {
			visitProto(t, n, parent);
		}
		
		if (ntype==Token.FUNCTION) {
			visitFunc(t, n, parent);
		}
		else if (ntype==Token.RETURN) {
			visitReturn(t, n, parent);
		}
		else if (ntype==Token.CALL) {
			visitCall(t, n, parent);
		}
		else if (ntype==Token.GETELEM || ntype==Token.GETPROP) {
			if (ptype==Token.ASSIGN && n == parent.getFirstChild()) {
				visitSet(t, n, parent);
			}
			else {
				visitGet(t, n, parent);
			}
		}
		else if (n.getChildCount()==2 && ntype!=Token.BLOCK && ntype!=Token.SCRIPT && ntype!=Token.ASSIGN) {
		//else if (ntype==Token.ADD || ntype==Token.DIV) {
			System.out.println(n);
			System.out.println(parent.toStringTree());
			visitOps(t, n, parent);
		}
		else if (ntype==Token.STRING || ntype==Token.NUMBER || ntype==Token.NULL 
			  || ntype==Token.TRUE || ntype==Token.FALSE
			  || (ntype==Token.NAME && n.getString()=="undefined") ) {
			if (ntype==Token.STRING && ptype==Token.GETPROP) {				
				// supposed to be empty
			}
			else {
				visitConst(t, n, parent);
			}
		}
		
		boolean cond = false;
		cond =( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
		//     || ntype==Token.CALL || ntype==Token.NEW
             || ptype == Token.FOR && parent.getChildAtIndex(1) == n );
		if (cond) {
			visitCond(t, n, parent);
		}
	}
}
