package ca.ubc.salt.concolicjs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class CVCnode {
	Map<String, CVCnode> nameToNode;
	Set<String> aliases;
	
	CVCnode parent;
	int order;
	Set<CVCnode> children;	
		
	public CVCnode(Map<String, CVCnode> nameToNode) {
		this.nameToNode = nameToNode;
		this.aliases	= new HashSet<String>();
		this.children 	= new HashSet<CVCnode>();
		this.order 		= -2;
	}
	
	public void addName(String name) {
		aliases.add(name);
	}
	
	public CVCnode getParent() {
		return this.parent;
	}
	
	public void setParent(CVCnode parent) {
		if (this.parent == null) {
			this.parent = parent;
			parent.children.add(this);
		}
		else if (this.parent != parent) {
			this.parent.merge(parent);
		}		
	}
	
	public void setOrder(int order) {
		this.order = order;
	}
	
	public void merge(CVCnode node) {		
		if (this.equals(node)) {
			return;
		}				
		Set<String> aliases = node.aliases;
		Iterator<String> itr_str = aliases.iterator();
		while (itr_str.hasNext()) {
			String name = itr_str.next();
			nameToNode.put(name, this);
		}
		this.aliases.addAll(aliases);
		
		Set<CVCnode> children = node.children;
		Iterator<CVCnode> itr_cvc = children.iterator();
		while (itr_cvc.hasNext()) {
			itr_cvc.next().parent = this;
		}
		this.children.addAll(children);
		
		node.parent.children.remove(node);
		node.parent.children.add(this);		
		this.setParent(node.parent);
		
		if (this.order == -2) {
			this.order = node.order;
		}
		else if (this.order > 0 && node.order > 0 && this.order != node.order) {
			System.out.println("order conflict when merging: "+ this.order +"("+ this.aliases.toString() +")  vs. "+ node.order +"("+ aliases.toString() +")");
		}
	}

	public Element toDOM(Document document) {				
		String[] ary = this.aliases.toArray(new String[this.aliases.size()]);
		Element elem = document.createElement(ary[0]);					
		Iterator<CVCnode> itr_cvc = this.children.iterator();
		while (itr_cvc.hasNext()) {			
			elem.appendChild(itr_cvc.next().toDOM(document));
		}
		return elem;
	}	
	
	public static void main(String[] args) {
		
	}
}
