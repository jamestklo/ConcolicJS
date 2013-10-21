package ca.ubc.tklo.cvc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
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
	}

	protected List<CVCnode> orderChildren() {
		int max = -1;
		Map<Integer, CVCnode> map = new HashMap<Integer, CVCnode>();
		Set<CVCnode> remaining = new HashSet<CVCnode>();
		Iterator<CVCnode> itr_cvc = this.children.iterator();
		while (itr_cvc.hasNext()) {
			CVCnode iterated = itr_cvc.next();
			int position = iterated.position;			
			if (position < 0) {				
				remaining.add(iterated);
			}
			else {
				if (position > max) {
					max = position;
				}
				CVCnode node = map.get(position);
				if (node instanceof CVCnode) {
					node.merge(iterated);					
				}					
				else {
					map.put(position, iterated);
				}				
			}
		}
		itr_cvc = remaining.iterator();
		while (itr_cvc.hasNext()) {
			CVCnode iterated = itr_cvc.next();
			int position = iterated.calPosition();
			if (position > max) {
				max = position;
			}
			iterated.setPosition(position);
			CVCnode node = map.get(position);
			if (node instanceof CVCnode) {
				node.merge(iterated);					
			}
			else {
				map.put(position, iterated);
			}			
		}
		
		List<CVCnode> ordered = new ArrayList<CVCnode>();
		
		for (int i=0; i <= max; i++) {
			ordered.add(map.get(i));
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
			if (xmlg.getCVC().childIndexEQ(this.getName(), m)) {
				return m;
			}
			else if (xmlg.getCVC().childIndexGT(this.getName(), m)) {
				l = m + 1;
			}
			else {
				h = m - 1;
			}
		}
		return m;
	}
	
	public Element toDOM(Document document) {												
		Element elem = document.createElement(this.getName());
		ListIterator<CVCnode> itr = this.orderChildren().listIterator(); 
		while (itr.hasNext()) {
			elem.appendChild(itr.next().toDOM(document));
		}
		return elem;
	}	
}
