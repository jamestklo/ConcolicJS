package edu.ubc.javascript;


import com.google.common.base.Supplier;
import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public class TraceCondVisitor implements Callback {

	private String condNamePrefix = "JSCompiler_cond_";
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
		enterCond.addChildrenToBack(Node.newString(Token.STRING, NodeUti1.getURL()));
		enterCond.addChildrenToBack(Node.newNumber(n.getLineno()));
		enterCond.addChildrenToBack(Node.newString(Token.STRING, Token.name(n.getType())));
		enterCond.addChildrenToBack(Node.newString(Token.STRING, Token.name(parent.getType())));
		enterCond.addChildrenToBack(Node.newString(num));
		
		Node exitCond = new Node(Token.CALL);						
		comma.addChildrenToBack(exitCond);
		exitCond.addChildrenToFront(Node.newString(Token.NAME, "__condExit"));
		exitCond.addChildrenToBack(Node.newString(varname));
		exitCond.addChildrenToBack(cloned);
		
	}

	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
		int ntype = n.getType();
		int ptype = (parent == null)?Token.NULL:parent.getType();
		if (ntype == Token.EMPTY || ntype == Token.NULL) {
			return;
		}
		if ( ((ptype==Token.IF || ptype==Token.HOOK || ptype==Token.SWITCH) && parent.getFirstChild() == n)
		  || ptype == Token.FOR && parent.getChildAtIndex(1) == n) {
			visitCond(t, n, parent);
		}
	}
}
