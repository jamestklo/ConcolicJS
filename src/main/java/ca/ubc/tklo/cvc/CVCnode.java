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
	
	String tag;
	Map<String, String> attributes;
	
	int position;
		
	public CVCnode(XMLgenerator xmlg) {
		this.xmlg 		= xmlg;
		this.aliases	= new HashSet<String>();
		this.children 	= new HashSet<CVCnode>();
		this.position 	= -2;
		this.attributes = new HashMap<String, String>();
	}
	
	public void addName(String name) {
		aliases.add(name);
	}
	public String setTag(String tag) {
		String old = this.tag;
		this.tag = tag;
		return old;
	}
	public String setAttribute(String key, String value) {
		return attributes.put(key, value);
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
	
	Set<String> getAliases() {
		return aliases;
	}
	
	public String getTag() {
		if (this.tag == null) {
			return xmlg.getDefaultTag();
		}
		return this.tag;
	}
	
	public String getName() {
		String nodeID = this.attributes.get("id");
		if (nodeID != null) {
			return nodeID;
		}
		return this.getAlias(0);
	}
	
	public String getAlias(int index) {
		if (index < 0) {
			return this.attributes.get("id");
		}
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
		if (this.equals(node) || node.position==-3) {
			return;
		}		
		Iterator<String> itr_str = node.aliases.iterator();
		while (itr_str.hasNext()) {
			xmlg.put(itr_str.next(), this);
		}
		aliases.addAll(node.aliases);
		
		Iterator<CVCnode> itr_cvc = node.children.iterator();
		while (itr_cvc.hasNext()) {
			itr_cvc.next().parent = this;
		}
		children.addAll(node.children);
		
		if (node.parent instanceof CVCnode) {
		  node.parent.children.remove(node);
		  this.setParent(node.parent);
		}
		
		this.setPosition(node.position);
		node.position = -3;
		
		if (this.tag == null) {
			this.tag = node.tag;
		}
		
		itr_str = node.attributes.keySet().iterator();
		while(itr_str.hasNext()) {
			String key = itr_str.next();
			if (! attributes.containsKey(key)) {
				attributes.put(key, node.attributes.get(key));
			}
		}
	}

	protected List<CVCnode> orderChildren() {
		int max = -1;
		Map<Integer, CVCnode> map = new HashMap<Integer, CVCnode>();
		Set<CVCnode> remaining = new HashSet<CVCnode>();
		Iterator<CVCnode> itr_cvc = this.children.iterator();
		Set<CVCnode> set2 = new HashSet<CVCnode>();
		while (itr_cvc.hasNext()) {
			set2.add(itr_cvc.next());
		}
		itr_cvc = set2.iterator();
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
			CVCnode node = map.get(i);
			if (node instanceof CVCnode) {
				ordered.add(map.get(i));
			}
			// fillers
			else {
				node = new CVCnode(this.xmlg);
				node.parent = this;
				node.position = i;
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
		Element elem = document.createElement(this.getTag());
		Iterator<String> itr_str = attributes.keySet().iterator();
		while (itr_str.hasNext()) {
			String key = itr_str.next();
			elem.setAttribute(key, attributes.get(key));
		}
		
		String id = elem.getAttribute("id"); 
		if (id == null || id.length() == 0) {
			elem.setAttribute(xmlg.getCVC().getSessionID(), getName());			
		}

		ListIterator<CVCnode> itr = this.orderChildren().listIterator(); 
		while (itr.hasNext()) {
			elem.appendChild(itr.next().toDOM(document));
		}
		return elem;
	}	
}
