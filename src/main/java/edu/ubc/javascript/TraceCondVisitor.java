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

	private String condNamePrefix = "JSCompiler_cond_";
	private void visitCond(NodeTraversal t, Node n, Node parent) {
		String num = safeNameIdSupplier.get();
		String varname = condNamePrefix + num;
		/*
		int etypes[] = {-1};					
		Node expr = ExpressionDecompositionVisitor.detectAncestor(n, etypes);		
		expr.getParent().addChildBefore(NodeUtil.newVarNode(varname, null), expr);
		*/		
		
		Node comma = new Node(Token.COMMA);
		Node cloned = n.cloneTree();
		tx.replace(n, comma, cloned);		
				
		Node enterCond = new Node(Token.CALL);
		comma.addChildrenToFront(enterCond);
		enterCond.addChildrenToFront(Node.newString(Token.NAME, "__condEnter"));
		enterCond.addChildrenToBack(Node.newString(varname));
		enterCond.addChildrenToBack(Node.newString(NodeUti1.getURL()));
		enterCond.addChildrenToBack(Node.newNumber(n.getLineno()));
		enterCond.addChildrenToBack(Node.newString(Token.name(n.getType())));
		enterCond.addChildrenToBack(Node.newString(Token.name(parent.getType())));
		enterCond.addChildrenToBack(Node.newString(num));
		
		Node exitCond = new Node(Token.CALL);						
		comma.addChildrenToBack(exitCond);
		exitCond.addChildrenToFront(Node.newString(Token.NAME, "__condExit"));
		exitCond.addChildrenToBack(Node.newString(varname));
		exitCond.addChildrenToBack(cloned);		
	}

	private String funcNamePrefix = "JSCompiler_func_";
	private void visitFunc(NodeTraversal t, Node n, Node parent) {
		Node block = n.getChildAtIndex(2);		
		Node target = block.getFirstChild();
		if (target==null) {
			return;
		}

		String num = safeNameIdSupplier.get();
		String varname = funcNamePrefix + num;
		Node name = n.getFirstChild();
		if (name.getString().length() < 1) {
			name.setString(varname);
		}
		
		Node enterFunc = new Node(Token.CALL);
		enterFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcEnter"));
		enterFunc.addChildrenToBack(Node.newString(varname));
		enterFunc.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
		enterFunc.addChildrenToBack(Node.newNumber(n.getLineno()));
		enterFunc.addChildrenToBack(Node.newString(name.getString()));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "this"));
		enterFunc.addChildrenToBack(Node.newString(Token.NAME, "arguments"));
		enterFunc.addChildrenToBack(Node.newString(num));		
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
		catc.addChildrenToFront(Node.newString(Token.NAME, varname+"e"));
		catb = new Node(Token.BLOCK);
		catc.addChildrenToBack(catb);
				
		Node exitFunc = new Node(Token.CALL);
		catb.addChildrenToBack(exitFunc);
		exitFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcExit"));
		
		Node thrw = new Node(Token.THROW);
		catb.addChildrenToBack(thrw);
		thrw.addChildrenToFront(Node.newString(Token.NAME, varname+"e"));
		
		blck.addChildrenToBack(exitFunc.cloneNode());
		tx.replace(block, blck, cloned);
	}
	
	private void visitReturn(NodeTraversal t, Node n, Node parent) {
		Node target = n.getFirstChild();
		if (target == null) {
			target = Node.newString(Token.NAME, "undefined");
			n.addChildrenToFront(target);
		}
		int ftypes[] = {Token.FUNCTION};
		Node func = NodeUti1.detectAncestor(parent, ftypes);
		//if (! varnames.containsKey(func)) {
			//visitFunc(t, func, func.getParent());
		//}

		Node cloned = target.cloneTree();
		Node exitFunc = new Node(Token.CALL);
		exitFunc.addChildrenToFront(Node.newString(Token.NAME, "__funcExit"));
		//exitFunc.addChildrenToBack(Node.newString(""));
		//exitFunc.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
		//exitFunc.addChildrenToBack(Node.newNumber(func.getLineno()));
		//exitFunc.addChildrenToBack(Node.newString(func.getFirstChild().getString()));		
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
		
		boolean cond;
		//cond =( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
        //     || ptype == Token.FOR && parent.getChildAtIndex(1) == n );
		cond = ntype==Token.CALL || ntype==Token.NEW;
		if (cond) {
			//visitCond(t, n, parent);
		}		
		else if (ntype==Token.FUNCTION){
			visitFunc(t, n, parent);
		}
		else if (ntype==Token.RETURN) {
			visitReturn(t, n, parent);
		}
	}
}
