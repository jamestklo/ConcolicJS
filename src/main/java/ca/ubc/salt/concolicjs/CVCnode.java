package ca.ubc.salt.concolicjs;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

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
		this.aliases = new HashSet<String>();
		this.children = new HashSet<CVCnode>();
		this.order = -2;
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
			nameToNode.put(itr_str.next(), this);
		}
		this.aliases.addAll(aliases);
		
		Set<CVCnode> children = node.children;
		Iterator<CVCnode> itr_cvc = children.iterator();
		while (itr_cvc.hasNext()) {
			itr_cvc.next().parent = this;
		}
		this.children.addAll(children);
		
		this.setParent(node.parent);
	}

	public Element toDOM(Document document) {				
		String[] ary = this.aliases.toArray(new String[this.aliases.size()]);
		Element elem = document.createElement(ary[0]);			
		Set<CVCnode> children = this.children;
		Iterator<CVCnode> itr_cvc = children.iterator();
		while (itr_cvc.hasNext()) {
			elem.appendChild(itr_cvc.next().toDOM(document));				
		}
		return elem;
	}	
	
	public static void main(String[] args) {
		
	}
}
