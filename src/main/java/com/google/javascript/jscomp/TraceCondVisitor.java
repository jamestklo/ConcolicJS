package com.google.javascript.jscomp;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.google.common.base.Supplier;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

import edu.ubc.javascript.NodeUti1;
import edu.ubc.javascript.ReflectiveNodeTransformer;
public class TraceCondVisitor implements Callback {

	private final Supplier<String> safeNameIdSupplier;
	private final String temp;
	private final ReflectiveNodeTransformer tx;
	public TraceCondVisitor(Compiler c, ReflectiveNodeTransformer tx) {
		safeNameIdSupplier = c.getUniqueNameIdSupplier();
		temp = "__t";
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
		String num = getNodeNum(n);
		String funcname = n.getFirstChild().getString();		
		String nodeType = Token.name(n.getType());
		
		Node block = n.getChildAtIndex(2);	
		Node target = block.getFirstChild();
		if (target!=null) {
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
		}
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
			return Node.newString(Token.NAME, getFuncName(getNodeNum(root))+"_c");
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
		cloned.setType(Token.CALL);
		Node fname = cloned.getFirstChild();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		Iterator<Node> itr = n.children().iterator();
		Iterator<Node> ctr = cloned.children().iterator();
		if (fname.getType()!=Token.FUNCTION) {
			itr.next();
			ctr.next();
		}
		while (ctr.hasNext() && itr.hasNext()) {
			orgs.put(ctr.next(), itr.next());
		}
		
		Node name = n.getFirstChild();
		switch (fname.getType()) {
		case Token.GETELEM:
		case Token.GETPROP:									
			cloned.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(n.getType()) +"GET"));						
			Node target = fname.removeFirstChild();
			Node key = fname.removeFirstChild();				
			cloned.addChildBefore(target, fname);
			cloned.addChildBefore(key, fname);
			cloned.removeChild(fname);			
			orgs.put(target, name.getFirstChild());
			orgs.put(key, name.getLastChild());
			break;
		default:
			cloned.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(n.getType())));
			orgs.put(fname, name);
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
		
		String callname = Token.name(parent.getType()).replace("ASSIGN", "SET");
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+callname));
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
		tx.replace(n, call, orgs);		
	}
	
	private void visitValue(NodeTraversal t, Node n, Node parent) {
		Node child = n.getFirstChild();
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_VALUE"));
		Node cloned = child.cloneTree();
		call.addChildrenToBack(cloned);		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, child);
		tx.replace(child, call, orgs);
	}
	
	private void visitAndOr(NodeTraversal t, Node n, Node parent) {
		int ntype = n.getType();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		
		Node n1 = n.getFirstChild();
		Node c1 = n1.cloneTree();
		orgs.put(c1, n1);

		Node comma = new Node(Token.COMMA);
		Node equal = new Node(Token.ASSIGN);
		comma.addChildrenToFront(equal);
		//Node temp1 = Node.newString(Token.NAME, "JSCompiler_"+ Token.name(ntype) +"_"+ safeNameIdSupplier.get());
		Node temp1 = Node.newString(Token.NAME, temp);
		comma.addChildrenToBack(temp1);	
		equal.addChildrenToFront(temp1.cloneTree());
		equal.addChildrenToBack(c1);

		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(ntype)));
		call.addChildrenToBack(comma);
		
		Node andor = new Node(ntype);
		call.addChildrenToBack(andor);
		Node call1 = new Node(Token.CALL);		
		call1.addChildrenToFront(Node.newString(Token.NAME, "__getValue"));
		call1.addChildrenToBack(temp1.cloneTree());
		andor.addChildrenToFront(call1);
		
		Node n2 = n.getLastChild();		
		Node c2 = n2.cloneTree();
		orgs.put(c2, n2);		
		andor.addChildrenToBack(c2);	
				
		tx.replace(n, call, orgs);
	}
	
	private void visitOps(NodeTraversal t, Node n, Node parent) {
		Node n1 = n.getFirstChild();
		Node c1 = n1.cloneTree();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(c1, n1);
		
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(n.getType())));
		call.addChildrenToBack(c1);
		
		if (n.getChildCount() > 1) {
			Node n2 = n.getLastChild();		
			Node c2 = n2.cloneTree();
			call.addChildrenToBack(c2);
			orgs.put(c2, n2);	
		}		
		tx.replace(n, call, orgs);
	}
	private void visitTypeof(NodeTraversal t, Node n, Node parent) {
		Node n1 = n.getFirstChild();
		Node c1 = n1.cloneTree();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(c1, n1);

		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+ Token.name(n.getType())));
		if (n1.getType()==Token.NAME){
			Node hook = new Node(Token.HOOK);
			call.addChildrenToBack(hook);
		
			Node sheq = new Node(Token.SHEQ);
			hook.addChildrenToFront(sheq);
		
			Node tyof = new Node(Token.TYPEOF);
			sheq.addChildrenToFront(tyof);
			tyof.addChildrenToFront(c1);				
			sheq.addChildrenToBack(Node.newString("undefined"));
		
			hook.addChildrenToBack(Node.newString(Token.NAME, "undefined"));
			hook.addChildrenToBack(c1.cloneTree());		
		}
		else {
			call.addChildrenToBack(c1);
		}
		tx.replace(n, call, orgs);		
	}
	private void visitInc(NodeTraversal t, Node n, Node parent) {
		int ntype = n.getType();
		Boolean incrdecr = (ntype==Token.INC || ntype==Token.DEC)?n.getBooleanProp(Node.INCRDECR_PROP):null;

		Node left = n.getFirstChild();
		int ltype = left.getType();
		Node cloned = left.cloneTree();
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, left);
		
		String callname = Token.name(ntype);
		if (callname.contains("ASSIGN_")) {
			callname = callname.substring(7);			
		}
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, "_"+callname));		
		call.addChildrenToBack(cloned);
		if (n.getChildCount() > 1) {
			Node right = n.getLastChild();
			Node clonedR = right.cloneTree();
			orgs.put(clonedR, right);
			call.addChildrenToBack(clonedR);
		}
		
		if (ltype==Token.NAME) {
			Node assign = new Node(Token.ASSIGN);
			assign.addChildrenToFront(cloned.cloneTree());
			assign.addChildrenToBack(call);
			
			int ptype = parent.getType();
			if (incrdecr!= null && incrdecr==true 
			 && ptype!=Token.EXPR_RESULT && NodeUti1.isStatement(n)!=true 
			 && (ptype!=Token.FOR || n!=parent.getChildAtIndex(2)) ) {
				
				Node comma = new Node(Token.COMMA);
				comma.addChildrenToBack(Node.newString(Token.NAME, temp));
				
				Node comma1 = new Node(Token.COMMA);
				comma.addChildrenToFront(comma1);				
				comma1.addChildrenToBack(assign);
								
				Node assign1 = new Node(Token.ASSIGN);
				comma1.addChildrenToFront(assign1);
				assign1.addChildrenToFront(Node.newString(Token.NAME, temp));
				assign1.addChildrenToBack(cloned.cloneTree());
				
				tx.replace(n, comma, orgs);
			}
			else {
				tx.replace(n, assign, orgs);
			}
		}
		else {
			if (ltype==Token.GETELEM || ltype==Token.GETPROP) {
				orgs.remove(cloned);				
				Node target = cloned.removeFirstChild();
				Node key = cloned.removeFirstChild();
				Node gett = new Node(Token.CALL);
				gett.addChildrenToFront(Node.newString(Token.NAME, "_GET"));
				gett.addChildrenToBack(target);
				gett.addChildrenToBack(key);
				gett.addChildrenToBack(Node.newNumber(1));
				orgs.put(target, left.getFirstChild());
				orgs.put(key, left.getLastChild());
				call.replaceChild(cloned, gett);

				if (incrdecr == null || incrdecr==false) {
					call.addChildrenToBack(Node.newNumber(1));
				}
				else {
					call.addChildrenToBack(new Node(Token.TRUE));
				}
			}
			else {
				//System.out.println(n.toStringTree());
			}
			tx.replace(n, call, orgs);
		}
	}
	protected void wrapFunction(Node n, String funcname) {
		Node cloned = n.cloneTree();				
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, funcname));
		call.addChildrenToBack(cloned);
		
		Map<Node, Node> orgs = new HashMap<Node, Node>();
		orgs.put(cloned, n);
		tx.replace(n, call, orgs);
	}
	private void visitForIn(NodeTraversal t, Node n, Node parent) {
		wrapFunction(n.getChildAtIndex(1), "__getValue");
	}
	private void visitThrow(NodeTraversal t, Node n, Node parent) {
		Node child0 = n.getFirstChild();
		if (child0.getType() == Token.STRING) {
			return;
		}
		wrapFunction(child0, "__getValue");
	}
	private void visitEval(NodeTraversal t, Node n, Node parent) {
		wrapFunction(n.getChildAtIndex(1), "__txCode");		
		/*Node child0 = n.getFirstChild();		
		int c0type = child0.getType();
		if (c0type == Token.NAME) {
			child0.setString("__evalNative");
		}*/		
	}
	
	private boolean isEval(Node n) {
		Node child0 = n.getFirstChild();
		int c0type = child0.getType();
		if (c0type == Token.NAME && child0.getString().equals("eval")) {
			return true;
		}
		else if (c0type == Token.GETPROP || c0type == Token.GETELEM) {
			Node child00 = child0.getFirstChild();
			if (child00.getType() == Token.NAME && child00.getString().equals("window")) {
				Node child01 = child0.getLastChild();
				if (child01.getType() == Token.STRING && child01.getString().equals("eval")) {
					return true;
				}
			}
		}		
		return false;
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {		
		boolean isJustPretty = false;
		int ntype = n.getType();
		int ptype = (parent == null)?Token.NULL:parent.getType();
		if (ntype == Token.EMPTY) {
			return;
		}
		else if (ntype == Token.SCRIPT) {
			//System.out.println(n.toStringTree());
		}
		if (isJustPretty) {
			if (ntype==Token.NEW && n.getFirstChild().getNext()==null) {
				n.addChildrenToBack(new Node(Token.EMPTY));
			}
			return;
		}
		else if ( (ntype==Token.STRING_KEY && n.getString().equals("__proto__"))
			   || (ntype==Token.CASE && NodeUti1.isConst(n.getFirstChild())==false) ) {
			visitValue(t, n, parent);
		}
		if (ntype==Token.FUNCTION) {
			visitFunc(t, n, parent);
		}
		else if (ntype==Token.RETURN) {
			visitReturn(t, n, parent);
		}
		else if (ntype==Token.CALL || ntype==Token.NEW) {
			if (isEval(n)==true) {
				visitEval(t, n, parent);			
			}
			else {
				visitCall(t, n, parent);
			}
		}
		else if (ntype==Token.GETELEM || ntype==Token.GETPROP) {
			if (ptype==Token.ASSIGN && n==parent.getFirstChild()) {
				visitSet(t, n, parent);
			}
			else if ((ptype==Token.CALL || ptype==Token.NEW) && n==parent.getFirstChild()) {
				// visitCall() will handle this
			}
			else {
				visitGet(t, n, parent);
			}
		}
		else if (ntype==Token.INC || ntype==Token.DEC || Token.name(ntype).contains("ASSIGN_") ) {
			visitInc(t, n, parent);
		}
		else if (ntype==Token.AND || ntype==Token.OR) {
			visitAndOr(t, n, parent);
		}
		//else if (n.getChildCount()==2 && ntype!=Token.BLOCK && ntype!=Token.SCRIPT && ntype!=Token.ASSIGN) {
		else if (ntype==Token.ADD	|| ntype==Token.SUB	|| ntype==Token.MUL || ntype==Token.DIV || ntype==Token.MOD // + - * /
			  || ntype==Token.NOT	|| ntype==Token.SHEQ|| ntype==Token.SHNE || ntype==Token.EQ || ntype==Token.NE // === !== == != 
			  || ntype==Token.GT	|| ntype==Token.GE	|| ntype==Token.LT || ntype==Token.LE // > >= < <=
			  || ntype==Token.POS	|| ntype==Token.NEG
			  || ntype==Token.IN || ntype==Token.INSTANCEOF) {
			visitOps(t, n, parent);
		}
		else if (ntype==Token.TYPEOF) {
			visitTypeof(t, n, parent);
		}
		else if (NodeUti1.isConst(n)) {
			if ((ptype==Token.GETPROP || ptype==Token.GETELEM) && parent.getFirstChild().equals(n)) {
				visitConst(t, n, parent);
			}
			else if (ntype==Token.STRING && (ptype==Token.GETPROP || ptype==Token.GETELEM || ptype==Token.REGEXP || ptype==Token.THROW)) {
				// the call to visitGet() will handle this case
			}
			else if (ptype==Token.CASE && n==parent.getFirstChild()) {				
			}
			else {
				visitConst(t, n, parent);
			}
		}
		else if (ntype == Token.THIS) {
			visitConst(t, n, parent);
		}
		else if (ntype==Token.FOR) {
			if (n.getChildAtIndex(2).getType() == Token.BLOCK) {
				visitForIn(t, n, parent);
			}
			else if (n.getChildAtIndex(1).getType() != Token.EMPTY) {
				visitCond(t, n.getChildAtIndex(1), n);
			}
		}
		else if (ntype==Token.DO) {
			visitCond(t, n.getChildAtIndex(1), n);
		}
		else if (ntype==Token.THROW) {
			visitThrow(t, n, parent);
		}
		
		boolean cond = false;
		cond =( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
		//     || ntype==Token.CALL || ntype==Token.NEW
			  );
		if (cond) {
			visitCond(t, n, parent);
		}
	}
}
