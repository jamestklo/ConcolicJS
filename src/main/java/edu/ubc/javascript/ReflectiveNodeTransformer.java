package edu.ubc.javascript;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public class ReflectiveNodeTransformer {
	private boolean isTxMode = true;
	private List<Node> nodes = new ArrayList<Node>();
	private List<Node[]> befores = new ArrayList<Node[]>();
	private List<Node[]> afters = new ArrayList<Node[]>(); 
	private List<Node> order = new ArrayList<Node>(); 
	private Map<Node, Node> replacing = new HashMap<Node, Node>();
	
	public int commit(boolean newTxMode) {
		isTxMode = newTxMode;
		int ret = nodes.size();
		ListIterator<Node> li_nodes = nodes.listIterator();
		ListIterator<Node[]> li_befores = befores.listIterator();
		ListIterator<Node[]> li_afters = afters.listIterator();		
		while(li_nodes.hasNext()) {
			_insert(li_nodes.next(), li_befores.next(), li_afters.next());
		}		
		nodes.clear();
		befores.clear();
		afters.clear();
				
		Iterator<Node> itr = order.iterator();
		while (itr.hasNext()) {
			Node n = itr.next();
			Node r;
			r = replacing.get(n);
			n.getParent().replaceChild(n, r);
			r = itr.next();
			r.getParent().replaceChild(r, n.cloneTree());
		}		
		return ret;
	}	
	
	public void replace(Node n, Node newNode, Node cloned) {
		if (isTxMode) {
			if (replacing.containsKey(n)) {
				cloned.getParent().replaceChild(cloned, replacing.get(n));
			}
			else {
				order.add(n);
				order.add(cloned);
			}
			replacing.put(n, newNode);		  
		}
		else {
			n.getParent().replaceChild(n, newNode);
		}
	}
	public void insert(Node n, Node[] before, Node[] after) {
		if (isTxMode) {
			nodes.add(n);
			befores.add(before);
			afters.add(after);
		}
		else {
			_insert(n, before, after);
		}
	}
	private void _insert(Node n, Node[] before, Node[] after) {
		// detect if it's a COMMA or EXPR_RESULT
		int types[] = {-1, Token.COMMA};
		Node ancestor = NodeUti1.isStatement(n)?n:NodeUti1.detectAncestor(n, types);
		Node parent = ancestor.getParent();	
		Node empty = new Node(Token.EMPTY);
		int blen = (before==null)?0:before.length;
		int alen = (after ==null)?0:after.length;
		
		if (NodeUti1.isStatement(ancestor)) {
			for (int i=0; i < blen; i++) {	
				Node inserted = before[i];
				int itype = inserted.getType();
				if (itype != Token.VAR && itype != Token.EXPR_RESULT) {
					inserted = new Node(Token.EXPR_RESULT);
					inserted.addChildrenToFront(before[i]);
				}
				parent.addChildBefore(inserted, ancestor);
			}
			for (int i=alen; i-- > 0;) {
				Node inserted = after[i];
				int itype = inserted.getType();
				if (itype != Token.VAR && itype != Token.EXPR_RESULT) {
					inserted = new Node(Token.EXPR_RESULT);
					inserted.addChildrenToFront(after[i]);
				}
				parent.addChildAfter(inserted, ancestor);
			}
		}
	    else if (ancestor.getType() == Token.COMMA) {
			if (blen > 0) {
				int start = 0;
				Node comma = ancestor.getFirstChild();
				if (NodeUti1.isAncestor(n, comma)) {
					Node first = comma;
					comma = new Node(Token.COMMA);
					ancestor.replaceChild(first, comma);
					comma.addChildrenToFront(before[0]);
					comma.addChildrenToBack(first);
					
					parent = ancestor;
					ancestor = comma;
					comma = before[0];
					start = 1;
				}
				ancestor.replaceChild(comma, empty);
				for (int i=start; i < blen; i++) {
					Node inserted = new Node(Token.COMMA);
					inserted.addChildrenToFront(comma);
					inserted.addChildrenToBack(before[i]);
					comma = inserted;
				}
				ancestor.replaceChild(empty, comma);
			}

			if (alen > 0) { 
				Node tparent = parent;
				if (parent.getType() != Token.COMMA) {
					Node comma = new Node(Token.COMMA);
					parent.replaceChild(ancestor, comma);
					comma.addChildrenToFront(ancestor);
					comma.addChildrenToBack(after[--alen]);
					parent = tparent = comma;
				}
				else if (NodeUti1.isAncestor(n, ancestor.getFirstChild())) {
					tparent = ancestor;
				}
				Node gparent = tparent.getParent();
				gparent.replaceChild(tparent, empty);
				Node child = tparent.getLastChild();
				tparent.removeChild(child);
	   
				Node comma = tparent;
				for (int i=0; i < alen; i++) {
					comma.addChildrenToBack(after[i]);
					Node inserted = new Node(Token.COMMA);	
					inserted.addChildrenToFront(comma);
					comma = inserted;	 
				}
				comma.addChildrenToBack(child);
				gparent.replaceChild(empty, comma);
			}			
		}
		
		if (n.getType()==Token.EMPTY) {
			n.getParent().removeChild(n);
		}

	}	
}
