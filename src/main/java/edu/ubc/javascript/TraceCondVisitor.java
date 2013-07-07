package edu.ubc.javascript;


import java.util.HashMap;
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
		tx.replace(n, comma, cloned);		
				
		Node enterCond = genCall("__condEnter", n, num);
		comma.addChildrenToFront(enterCond);
		enterCond.addChildrenToBack(Node.newString(Token.name(n.getType())));
		enterCond.addChildrenToBack(Node.newString(Token.name(parent.getType())));
		
		Node exitCond = genCall("__condExit", n, num); 			
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
				name.setString("JSCompiler_func_" + num);
			}
		}
		return num;
	}
	
	// problem: html file can have multiple <script> tags
	// goal: unique label for each logged AST node
	public static String getLabel(Node n, String num) {
		int scriptCount = NodeUti1.scriptCount.get();
		return Token.name(n.getType()) +" "+ NodeUti1.filename.get() + ((scriptCount>0)?"_"+scriptCount:"") + " "+ num;
	}
	
	public static Node genCall(String name, Node n, String num) {
		Node call = new Node(Token.CALL);
		call.addChildrenToFront(Node.newString(Token.NAME, name));
		call.addChildrenToBack(Node.newString(getLabel(n, num)));
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
		
		Node enterFunc = genCall("__funcEnter", n, num);				
		enterFunc.addChildrenToBack(Node.newString(funcname));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "this"));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "arguments"));
		Node before[] = {enterFunc};
		tx.insert(target, before, null);

		Node blck = new Node(Token.BLOCK);
		Node tryc = new Node(Token.TRY);
		blck.addChildrenToFront(tryc);
		Node cloned = block.cloneTree();
		tryc.addChildrenToFront(cloned);
		
		Node catb = new Node(Token.BLOCK);
		tryc.addChildrenToBack(catb);
		Node catc = new Node(Token.CATCH);
		catb.addChildrenToFront(catc);
		catc.addChildrenToFront(Node.newString(Token.NAME, funcname+"_e"));
		catb = new Node(Token.BLOCK);
		catc.addChildrenToBack(catb);
		
		Node exitExpr = new Node(Token.EXPR_RESULT);
		catb.addChildrenToBack(exitExpr);
		Node exitFunc = genCall("__funcExit", n, num);
		exitExpr.addChildrenToFront(exitFunc);
		Node exitFun2 = exitFunc.cloneTree();
		exitFunc.addChildrenToBack(Node.newString(Token.NAME, funcname+"_e"));
		
		Node thrw = new Node(Token.THROW);
		catb.addChildrenToBack(thrw);
		thrw.addChildrenToFront(Node.newString(Token.NAME, funcname+"_e"));
		
		blck.addChildrenToBack(exitFun2); // exception not thrown here
		tx.replace(block, blck, cloned);
		
		Node assign = new Node(Token.ASSIGN);
		Node getElem = new Node(Token.GETELEM);
		assign.addChildrenToFront(getElem);
		getElem.addChildrenToFront(Node.newString(Token.NAME, "__astGlobal"));
		getElem.addChildrenToBack(Node.newString(getLabel(n, num)));
		
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
	
	private void visitReturn(NodeTraversal t, Node n, Node parent) {
		Node target = n.getFirstChild();
		if (target == null) {
			target = Node.newString(Token.NAME, "undefined");
			n.addChildrenToFront(target);
		}
		int ftypes[] = {Token.FUNCTION};
		Node func = NodeUti1.detectAncestor(parent, ftypes);
		if (func.getType()==Token.FUNCTION) { 
			Node cloned = target.cloneTree();
			Node exitFunc = genCall("__funcExit", func, getNodeNum(func));
			exitFunc.addChildrenToBack(cloned);
			tx.replace(target, exitFunc, cloned);
		}
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
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
		else if (ntype==Token.FUNCTION){
			visitFunc(t, n, parent);
		}
		else if (ntype==Token.RETURN) {
			visitReturn(t, n, parent);
		}
	}
}
