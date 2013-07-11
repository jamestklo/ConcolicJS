package edu.ubc.javascript;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.google.common.base.Supplier;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.jscomp.Scope.Var;
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
		tx.replace(n, comma, cloned);
		
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
		tx.replace(block, blck, cloned);
		
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
			tx.replace(n, assign, n2);						
		}		
	}
	
	private Map<Var, String> scopeNum = new HashMap<Var, String>();	
	private void visitPARAM_LIST(NodeTraversal t, Node n, Node parent) {
		Node root = t.getScopeRoot();
		if (root != n.getParent()) {
			return;
		}
		String num = getNodeNum(root);
		Iterator<Var> vars = t.getScope().getVars();
		while(vars.hasNext()) {
			Var var = vars.next();
			scopeNum.put(var, num);
		}									
	}
	
	private void visitVar(NodeTraversal t, Node n, Node parent) {
		Node name = n.getFirstChild();
		Node value = name.getFirstChild();
		if (value == null) {
			value = Node.newString(Token.NAME, "undefined");
			n.addChildrenToFront(value);
		}
		
		Node cloned = value.cloneTree();
		Node newVar = new Node(Token.CALL);
		newVar.addChildToFront(Node.newString(Token.NAME, "_VAR"));
		Node root = t.getScopeRoot();
		if (root.getType()==Token.FUNCTION) {
			newVar.addChildrenToBack(Node.newString(Token.NAME, getFuncName(getNodeNum(root))));
		}
		else {
			newVar.addChildrenToBack(new Node(Token.NULL));
		}
		newVar.addChildrenToBack(Node.newString(n.getString()));
		newVar.addChildrenToBack(cloned);
		tx.replace(value, newVar, cloned);
	}
	
	private void visitName(NodeTraversal t, Node n, Node parent) {
		/*int ptype = parent.getType();
		if (ptype==Token.FUNCTION || ptype==Token.PARAM_LIST || ptype==Token.VAR) {
			return;
		}
		Scope scope = t.getScope();
		String name = n.getString();
		Node enterName = new Node(Token.CALL);
		enterName.addChildrenToFront(Node.newString(Token.NAME, "_NAME"));
		enterName.addChildrenToBack(Node.newString(Token.NAME, getFuncName(scopeNum.get(scope.getSlot(n.getString())))));
		enterName.addChildrenToBack(Node.newString(name));
		Node cloned = n.cloneTree();
		enterName.addChildrenToBack(cloned);*/		
		//tx.replace(n, enterName, cloned)
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
			tx.replace(target, exitFunc, cloned);
		}
	}
	
	private void visitCall(NodeTraversal t, Node n, Node parent) {
		Node fname = n.getFirstChild();
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
		System.out.println(n.toStringTree());
		int ntype = n.getType();
		int ptype = (parent == null)?Token.NULL:parent.getType();
		if (ntype == Token.EMPTY || ntype == Token.NULL) {
			return;
		}
		else if (ntype==Token.NEW && n.getFirstChild().getNext()==null) {
			n.addChildrenToBack(new Node(Token.EMPTY));
		}
		
		boolean cond=false;
		cond =( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
		//     || ntype==Token.CALL || ntype==Token.NEW
             || ptype == Token.FOR && parent.getChildAtIndex(1) == n );
		
		if (cond) {
			visitCond(t, n, parent);
		}
		else if (ntype==Token.FUNCTION) {
			visitFunc(t, n, parent);
		}
		else if (ntype==Token.RETURN) {
			visitReturn(t, n, parent);
		}
		/*else if (ntype==Token.PARAM_LIST) {
			visitPARAM_LIST(t, n, parent);
		}*/
		else if (ntype==Token.VAR) {
			//visitVar(t, n, parent);
		}
		else if (ntype==Token.CALL) {
			visitCall(t, n, parent);
		}
	}
}
