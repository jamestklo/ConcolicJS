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
				
		Node enterCond = new Node(Token.CALL);
		comma.addChildrenToFront(enterCond);
		enterCond.addChildrenToFront(Node.newString(Token.NAME, "__condEnter"));
		enterCond.addChildrenToBack(Node.newString(num));
		enterCond.addChildrenToBack(Node.newString(NodeUti1.getURL()));
		enterCond.addChildrenToBack(Node.newString(Token.name(n.getType())));
		enterCond.addChildrenToBack(Node.newString(Token.name(parent.getType())));
		
		Node exitCond = new Node(Token.CALL);						
		comma.addChildrenToBack(exitCond);
		exitCond.addChildrenToFront(Node.newString(Token.NAME, "__condExit"));
		exitCond.addChildrenToBack(Node.newString(num));
		exitCond.addChildrenToBack(Node.newString(NodeUti1.getURL()));
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
	private void visitFunc(NodeTraversal t, Node n, Node parent) {
		Node block = n.getChildAtIndex(2);		
		Node target = block.getFirstChild();
		if (target==null) {
			return;
		}

		String num = getNodeNum(n);
		String funcname = n.getFirstChild().getString();
				
		Node enterFunc = new Node(Token.CALL);
		enterFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcEnter"));
		enterFunc.addChildrenToBack(Node.newString(num));
		enterFunc.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
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
		Node exitFunc = new Node(Token.CALL);
		exitExpr.addChildrenToFront(exitFunc);
		exitFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcExit"));
		exitFunc.addChildrenToBack(Node.newString(num));
		exitFunc.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
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
		String split[] = NodeUti1.getURL().split("/");	
		getElem.addChildrenToBack(Node.newString(Token.name(n.getType())+" "+ split[split.length-1] +" "+ num));
		
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
		 
		Node cloned = target.cloneTree();
		Node exitFunc = new Node(Token.CALL);
		exitFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcExit"));
		exitFunc.addChildrenToBack(Node.newString(getNodeNum(func)));
		exitFunc.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
		exitFunc.addChildrenToBack(cloned);
		tx.replace(target, exitFunc, cloned);
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
		//cond =( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
		//     || ntype==Token.CALL || ntype==Token.NEW
        //     || ptype == Token.FOR && parent.getChildAtIndex(1) == n );
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
