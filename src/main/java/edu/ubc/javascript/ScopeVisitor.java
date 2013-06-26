/**
 * 
 */
package edu.ubc.javascript;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.Scope;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;
import com.google.javascript.rhino.jstype.JSType;
import com.google.javascript.rhino.jstype.StaticSlot;

public class ScopeVisitor implements NodeTraversal.Callback {

	public int count = 0;
	public Map<String, Set<Scope>> found = new HashMap<String, Set<Scope>>();
	public java.util.IdentityHashMap<Scope, String> scopes = new java.util.IdentityHashMap<Scope, String>();
	
	@Override
	public boolean shouldTraverse(NodeTraversal nodeTraversal, Node n, Node parent) {
		return true;
	}
	
	@Override
	public void visit(NodeTraversal t, Node n, Node parent) {
		TagManager.tagNode(n, "line", t.getLineNumber());
		String name = scopes.get(t.getScope());
		if(name == null) {
			scopes.put(t.getScope(), (count++)+"");
		}
		if(n.getType() == Token.NAME) {
			StaticSlot<JSType> slot = t.getScope().getSlot(n.getString());
			
			if(n.getString().equals("")) {
				return;
			}
						
			String scope = null;
			if(t.getScope().getParent() == null) {
				scope = "local";
			} 
			else {
				scope = findName(t.getScope(), n.getString(), 0 ,t.getScope(), n);
			}
			
			TagManager.tagNode(n, "scope", scope);
		}
	}

	String findName(Scope local, String name, int up, Scope root, Node n) {
		if((local.getParent() == null) ) {
			return "global";
		} 
		else {
			if(local.isDeclared(name, false)) {
				if(name.equals("undefined")) {
					System.out.print("");
				}
				if(up == 0) {
					return "local";
				} 
				else {
					String scopeName = scopes.get(local);
					Set<Scope> sc = found.get(scopeName+"." + name);
					if(sc == null) {
						sc = new HashSet<Scope>();
						found.put(scopeName+"." + name, sc);
					}
					sc.add(root);
					if(sc.size() > 1) {
						TagManager.tagNode(n, "multipleRefs", true);
					}
					return "up"+up;
				}
			} 
			else {
				return findName(local.getParent(), name, up+1, root, n);
			}
		}
	}

}