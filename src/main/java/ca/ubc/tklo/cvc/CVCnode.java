package ca.ubc.tklo.cvc;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class CVCnode {
	XMLgenerator xmlg;
	Set<String> aliases;
	CVCnode parent;
	Set<CVCnode> children;
	
	int position;
	//CVCnode prev;
	//CVCnode next;
		
	public CVCnode(XMLgenerator xmlg) {
		this.xmlg 		= xmlg;
		this.aliases	= new HashSet<String>();
		this.children 	= new HashSet<CVCnode>();

		this.position 	= -2;
		//this.prev		= null;
		//this.next		= null;
	}
	
	public void addName(String name) {
		aliases.add(name);
	}
	
	public void setParent(CVCnode parent) {
		if (parent instanceof CVCnode) {
			if (this.parent instanceof CVCnode) {
				this.parent.merge(parent);	
			}
			else {
				this.parent = parent;			
			}
			parent.children.add(this);
		}
	}
	
	public int setPosition(int position) {
		int oldPosition  = this.position;
		if (position != oldPosition && oldPosition < 0 && position >= -1) {			
			this.position = position;		
		}
		return oldPosition;		
	}
	
	/*public void setPrev(CVCnode prev) {		
		if (prev instanceof CVCnode) {
		  if (this.prev instanceof CVCnode) {
		    this.prev.merge(prev);			
		  }
		  else {
		    this.prev= prev;
		  }
		  prev.setNext(this);
		}		
	}	
	public void setNext(CVCnode next) {
		if (next instanceof CVCnode) {
		  if (this.next instanceof CVCnode) {		  
		    this.next.merge(next);
		  }
		  else {
		    this.next= next;
		  }
		  next.setPrev(this);
		}		
	}*/	

	
	public Set<String> getAliases() {
		return aliases;
	}
	
	public String getName() {
		return this.getName(0);
	}
	
	public String getName(int index) {  
		Set<String> aliases = this.aliases;
		int size = aliases.size();
		if (size == 0) {
			return "";
		}
		String[] ary = aliases.toArray(new String[size]);
		return ary[index%size];		
	}
	
	public CVCnode getParent() {
		return this.parent;
	}
			
	public void merge(CVCnode node) {		
		if (this.equals(node)) {
			return;
		}
		
		Set<String> aliases = node.aliases;
		Iterator<String> itr_str = aliases.iterator();
		while (itr_str.hasNext()) {
			xmlg.put(itr_str.next(), this);
		}
		this.aliases.addAll(aliases);
		
		Set<CVCnode> children = node.children;
		Iterator<CVCnode> itr_cvc = children.iterator();
		while (itr_cvc.hasNext()) {
			itr_cvc.next().parent = this;
		}
		this.children.addAll(children);
		
		CVCnode parent = node.parent;
		if (parent instanceof CVCnode) {
		  parent.children.remove(node);
		  this.setParent(parent);
		}
		
		this.setPosition(node.position);
		
		/*CVCnode prev = node.prev;		
		if (prev instanceof CVCnode) {
			prev.next = null;
			this.setPrev(prev);
		}
		
		CVCnode next = node.next;
		if (next instanceof CVCnode) {
			next.prev = null;
			this.setNext(next);	
		}*/
	}

	public ArrayList<CVCnode> orderChildren() {
		ArrayList<CVCnode> ordered = new ArrayList<CVCnode>();
		Set<CVCnode> remaining = new HashSet<CVCnode>();
		Iterator<CVCnode> itr_cvc = this.children.iterator();
		while (itr_cvc.hasNext()) {
			CVCnode iterated = itr_cvc.next();
			int position = iterated.position;			
			if (position < 0) {
				remaining.add(iterated);
			}
			else {
				CVCnode node = ordered.get(position);
				if (node instanceof CVCnode) {
					node.merge(iterated);					
				}
				else {
					ordered.set(position, iterated);
				}
			}
		}
		
		itr_cvc = remaining.iterator();
		while (itr_cvc.hasNext()) {
			CVCnode iterated = itr_cvc.next();
			int position = iterated.calPosition();
			iterated.setPosition(position);
			CVCnode node = ordered.get(position);
			if (node instanceof CVCnode) {
				node.merge(iterated);					
			}
			else {
				ordered.set(position, iterated);
			}			
		}
		
		return ordered;
	}
	
	protected int calPosition() {
		if (this.position >= 0) {
			return this.position;
		}
		CVCnode parent = this.parent;
		if (parent == null) {
			return 0;
		}
		
		int m=0, l=0, h=this.parent.children.size()-1;
	    while (l < h) {
			m = l + (h-l)/2;
			if (xmlg.childIndexEQ(this.getName(), m)) {
				return m;
			}
			else if (xmlg.childIndexGT(this.getName(), m)) {
				l = m + 1;
			}
			else {
				h = m - 1;
			}
		}
		return m;
	}
	
	/*private static void extend(CVCnode iterated, ArrayList<CVCnode> ordering, Set<CVCnode> remaining) {
		int position = iterated.position + 1;
		CVCnode sibling = iterated.next;
		while ((sibling instanceof CVCnode) && remaining.contains(sibling)) {
		  remaining.remove(sibling);
		  CVCnode ordered = ordering.get(position);
		  if (ordered instanceof CVCnode) {
		    ordered.merge(sibling);
		  }
		  else {
		    ordering.set(position, sibling);
		  }
		  ++position;
		  sibling = sibling.next;
		}
		position = iterated.position - 1;
		sibling = iterated.prev;
		while ((sibling instanceof CVCnode) && remaining.contains(sibling)) {
		  remaining.remove(sibling);			
		  CVCnode ordered = ordering.get(position);			  
		  if (ordered instanceof CVCnode) {
		    ordered.merge(sibling);
		  }
		  else {
		    ordering.set(position, sibling);
		  }
		  --position;
		  sibling = sibling.prev;
		}	
	}*/
	
	/*ArrayList<CVCnode> orderChildren() {		
		ArrayList<CVCnode> ordering = new ArrayList<CVCnode>();
		Set<CVCnode> remaining = new HashSet<CVCnode>();
		
		Iterator<CVCnode> itr_cvc = this.children.iterator();
		while (itr_cvc.hasNext()) {
			CVCnode iterated = itr_cvc.next();
			int position = iterated.position;			
			if (position == -2) {
				remaining.add(iterated);
			}
			else {
				CVCnode ordered = ordering.get(position);
				if (ordered instanceof CVCnode) {
					ordered.merge(iterated);					
				}
				else {
					ordering.set(position, iterated);
				}
			}
		}
		
		ListIterator<CVCnode> lst_cvc = ordering.listIterator();
		List<CVCnode> lst = new LinkedList<CVCnode>();
		while (lst_cvc.hasNext()) {
			lst.add(lst_cvc.next());
		}
		lst_cvc = lst.listIterator();
		while (lst_cvc.hasNext() && remaining.isEmpty()==false) {
			extend(lst_cvc.next(), ordering, remaining);
		}
		return ordering;
	}*/
	
	public Element toDOM(Document document) {												
		Element elem = document.createElement(this.getName());		
		ListIterator<CVCnode> itr_cvc = this.orderChildren().listIterator();
		while (itr_cvc.hasNext()) {
			elem.appendChild(itr_cvc.next().toDOM(document));
		}
		return elem;
	}	
	
	public static void main(String[] args) {
		
	}
}
