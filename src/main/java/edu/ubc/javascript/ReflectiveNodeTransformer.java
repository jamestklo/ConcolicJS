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
	
	private List<Node[]> curs = new ArrayList<Node[]>();
	private List<Map<Node, Node>> orgs = new ArrayList<Map<Node, Node>>();
	
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

		Map<Node, Node> latest = new HashMap<Node, Node>();		
		Iterator<Node[]> icur = curs.iterator();
		Iterator<Map<Node, Node>> iorg = orgs.iterator();
		while (icur.hasNext()) {
			Node ary[] = icur.next();
			Node old = ary[0];			
			Node cur = ary[1];
			old = latest.containsKey(old)?latest.get(old):old;
			old.getParent().replaceChild(old, cur);
			Map<Node, Node> org = iorg.next();

			Iterator<Node> ktr = org.keySet().iterator();
			while (ktr.hasNext()) {
				Node cloned = ktr.next();
				Node original = org.get(cloned);
				Node lat1 = latest.containsKey(original)?latest.get(original):original;
				Node par1 = lat1.getParent(); 
				if (par1 instanceof Node) {
					par1.removeChild(lat1);
				}
				cloned.getParent().replaceChild(cloned, lat1);
				latest.put(original, lat1);
			}
			latest.put(old, cur);
		}
		curs.clear();
		orgs.clear();
		return ret;
	}	
	
	public void replace(Node n, Node newNode, Map<Node, Node> originals) { 
		if (isTxMode) {
			Node ary[] = {n, newNode};
			curs.add(ary);
			orgs.add(originals);
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
