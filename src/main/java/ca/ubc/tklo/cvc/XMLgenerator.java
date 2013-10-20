package ca.ubc.tklo.cvc;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
/*
 *  remains to be done
 *  	1) ordering of children
 *  	2) extending XMLgenerator.java to cover attributes, tag names, etc.
 *  	3) handling conflicts
 */
public class XMLgenerator {	
	protected Map<String, CVCnode> nameToNode = new HashMap<String, CVCnode>();
	protected CVCsolverDOM cvc;
	protected Document document;
	public XMLgenerator(CVCsolverDOM cvc, BufferedReader reader) {
		this.cvc = cvc;
		parseSolverOutput(reader);
		this.document = toDOM(null);
	}
	protected CVCsolverDOM getCVC() {
		return cvc;
	}	
	protected Document getDocument() {
		return document;
	}
	protected CVCnode put(String key, CVCnode value) {
		return nameToNode.put(key, value);
	}	
	protected CVCnode getNode(String name) {
		CVCnode ret = nameToNode.get(name);
		if (ret == null) {
		  ret = new CVCnode(this);
		  ret.addName(name);
		  nameToNode.put(name, ret);
		}
		return ret; 
	}		
	protected CVCnode setParent(String child, String parent, int at) {		
		CVCnode childNode = getNode(child);
		CVCnode parentNode = childNode.parent;
		if (nameToNode.get(parent) == null && parentNode != null) {
			parentNode.addName(parent);
			nameToNode.put(parent, parentNode);
			childNode.setPosition(at);
			return childNode;
		}
		return setParent(child, getNode(parent), at);
	}	
	protected CVCnode setParent(String child, CVCnode parent, int at) {
		CVCnode childNode = getNode(child);
		childNode.setParent(parent);
		childNode.setPosition(at);
		return childNode;
	}		
	protected void setSibling(String prev, String next) {
		CVCnode prevNode = nameToNode.get(prev);
		CVCnode nextNode = nameToNode.get(next);
		if (prevNode instanceof CVCnode) {
			if (nextNode == null) {
		  		nextNode = setParent(next, prevNode.getParent(), -2);
		  	}
		}
		else if (nextNode instanceof CVCnode) {
			prevNode = setParent(prev, nextNode.getParent(), -2);	
		}
		else {
			CVCnode parent = new CVCnode(this);
			prevNode = setParent(prev, parent, -2);
			nextNode = setParent(next, parent, -2);	            
		}
		
		if (prevNode.position >= 0) {
			nextNode.setPosition(prevNode.position+1);				  
		}
		if (nextNode.position > 0) {
			prevNode.setPosition(nextNode.position-1);				  
		}

		//prevNode.setNext(nextNode);
		//nextNode.setPrev(prevNode);
	}
	private void parseSolverOutput(BufferedReader br) {					
		String regex0 = "(parent|children|firstChild|lastChild|following_sibling|preceding_sibling).*";
		Pattern p0 = Pattern.compile("[\\(,\\s\\)]");

		String regex1 = "\\(.* = .*\\);$";
		Pattern p1 = Pattern.compile("[\\(\\s=\\)]");			

		String line;
		try {
			for (int i=0; (line = br.readLine()) != null;) {
				if (line.length() > 6 && line.substring(0, 6).equals("ASSERT")) {					
					String relation = line.substring(7);
					if (relation.matches(regex0)) {
						String[] ary = p0.split(relation);
						System.out.println(i++ +" "+ relation +" "+ ary.length);
						if (ary.length > 4) {
							switch(ary[0]) {
							case("parent"):
								setParent(ary[3], ary[1], -2);
								break;
							case("children"):
								setParent(ary[1], ary[3], new Integer(ary[5]));
								break;
							case("firstChild"):
								setParent(ary[1], ary[3], 0);
								break;
							case("lastChild"):
								setParent(ary[1], ary[3], -1);
								break;
							case ("following_sibling"):
								setSibling(ary[3], ary[1]);
								break;																
							case ("preceding_sibling"):
								setSibling(ary[1], ary[3]);
								break;
							}													
						}
					}
					else if (relation.matches(regex1)) {
						String[] ary = p1.split(relation);
						System.out.println(i++ +" "+ relation +" "+ ary.length);
					}
				}
			}
			br.close();
		} 
		catch (IOException e) {
			e.printStackTrace();
		}		
	}	
	private Document toDOM(Document document) {							
		try {
			if (document == null) {
				document = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
			}
			// find root
			Set<CVCnode> roots = new HashSet<CVCnode>();		
			Iterator<CVCnode> itr_cvc = nameToNode.values().iterator();
			while (itr_cvc.hasNext()) {
				CVCnode node = itr_cvc.next();
				if (node.getParent() == null) {
					roots.add(node);
				}
			}
			itr_cvc = roots.iterator();		
			while (itr_cvc.hasNext()) {			
				document.appendChild(itr_cvc.next().toDOM(document));
			}						
		}
		catch (ParserConfigurationException e) {
			e.printStackTrace();
		}			
		return document;		
	}	
	public static void outXML(Document document, OutputStream out) {
		try {
			//XML specific representation output (exact details not relevant)
			TransformerFactory tf = TransformerFactory.newInstance();
			Transformer transformer = tf.newTransformer();
			transformer.transform(new DOMSource(document), new StreamResult(out));
		}
		catch(Exception e) {
			throw new RuntimeException(e);
		}
	}	
	protected Set<CVCnode> getNodeSet() {
		Set<CVCnode> set = new HashSet<CVCnode>();
		Iterator<String> itr_str = nameToNode.keySet().iterator();
		while (itr_str.hasNext()) {
			set.add(nameToNode.get(itr_str.next()));
		}
		return set;
	}
	
	public static void main(String[] args) {
		CVCsolverDOM csd = null;
		try {
			XMLgenerator xmlg = new XMLgenerator(csd, new BufferedReader(new FileReader("Z:/cvc4/cvc3-output20131010.txt")) );
			outXML(xmlg.toDOM(null), System.out);
			System.out.println("\n");
			
			Iterator<CVCnode> itr_cvc = xmlg.getNodeSet().iterator();
			while (itr_cvc.hasNext()) {
				System.out.println(itr_cvc.next().getAliases().toString());
			}
		} 
		catch (FileNotFoundException e) {
			e.printStackTrace();
		}			
	}
}
