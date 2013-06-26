/**
 * 
 */
package edu.ubc.javascript;

import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public class ClosureCheck implements NodeTraversal.Callback {
	
	private ScopeVisitor sv;
	
	public ClosureCheck(ScopeVisitor sv) {
		this.sv = sv;
	}
	
	@Override
	public boolean shouldTraverse(NodeTraversal nodeTraversal, Node n, Node parent) {
		return true;
	}

	public int count = 0;
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
		String name = sv.scopes.get(t.getScope());
		if(name == null) {
			name = (count++)+"";
			sv.scopes.put(t.getScope(), name);
		}
		if(n.getType() == Token.NAME) {
			if(n.getString().equals("")) {
				return;
			}
			String varName = n.getString();
		
			if(sv.found.containsKey(name + "." + varName)) {
				TagManager.tagNode(n, "isClosed", true);
				TagManager.tagNode(n, "referents", sv.found.get(name + "." + varName).size());
			}			
		}
	}
}