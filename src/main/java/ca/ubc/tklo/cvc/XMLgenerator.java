package ca.ubc.tklo.cvc;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
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
import org.w3c.dom.Element;

import com.google.common.base.Joiner;
/*
 *  remains to be done
 *  	1) extending XMLgenerator.java to cover attributes, tag names, etc.
 */
public class XMLgenerator {	
	protected Map<String, CVCnode> nameToNode = new HashMap<String, CVCnode>();
	protected CVCsolverDOM cvc;
	protected Document document;
	protected CVCnode root;
	public XMLgenerator(CVCsolverDOM cvc, BufferedReader reader) {
		this.cvc = cvc;
		parseSolverOutput(reader);
		Iterator<String> itr = cvc.getNodeIDs().iterator();
		while (itr.hasNext()) {
			String nodeID = itr.next();
			CVCnode node = nameToNode.get(nodeID);			
			if (node instanceof CVCnode) {
				node.setAttribute("id", nodeID);
			}			
		}
		itr = cvc.getTempIDs().iterator();
		String sessionID = cvc.getSessionID();
		while (itr.hasNext()) {
			String tempID = itr.next();
			CVCnode node = nameToNode.get(tempID);		
			if (node instanceof CVCnode) {
				node.setAttribute(sessionID, tempID);
			}			
		}
	}
	public String getDefaultTag() {
		return "span";
	}
	protected CVCsolverDOM getCVC() {
		return cvc;
	}	
	protected Document getDocument() {
		if (document == null) {
			document = toDOM(null);
		}
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
	protected CVCnode setRoot(String name) {
		CVCnode node = getNode(name);
		if (root instanceof CVCnode) {
			root.merge(node);
		}
		else {
			root = node;
		}
		return root;
	}
	protected CVCnode setParent(String child, CVCnode parent, int at) {
		CVCnode childNode = getNode(child);
		childNode.setParent(parent);
		childNode.setPosition(at);
		return childNode;
	}		
	protected void setSibling(String prev, String next) {
		CVCnode prevNode = getNode(prev);
		CVCnode prevParent = prevNode.getParent();
		CVCnode nextNode = getNode(next);
		CVCnode nextParent = nextNode.getParent();
		
		if (prevParent instanceof CVCnode) {
			nextNode.setParent(prevParent);						
		}
		else if (nextParent instanceof CVCnode) {
			prevNode.setParent(nextParent);
		}
		else {
			CVCnode parent = new CVCnode(this);
			prevNode.setParent(parent);
			nextNode.setParent(parent);
		}
		if (prevNode.position >= 0) {
			nextNode.setPosition(prevNode.position+1);				  
		}
		else if (nextNode.position > 0) {
			prevNode.setPosition(nextNode.position-1);				  
		}

		//prevNode.setNext(nextNode);
		//nextNode.setPrev(prevNode);
	}
	private int count(String str, String substr) {
		int lastIndex = 0;
		int count =0;
		while(lastIndex != -1) {
			lastIndex = str.indexOf(substr, lastIndex);
			if( lastIndex != -1){
				count ++;
				lastIndex+=substr.length();
			}
	    }
	    return count;
	}
	private void parseSolverOutput(BufferedReader br) {					
		String regex0 = ".*(parent|child|children|firstChild|lastChild|nextSibling|previousSibling|following_sibling|preceding_sibling|root).*";
		//String regex1 = "\\(.* = .*\\);$";
		String regex2 = ".*(NOT|FORALL|EXISTS).*";
		Pattern p0 = Pattern.compile("[\\(,\\s\\)]");
		//Pattern p1 = Pattern.compile("[\\(\\s=\\)]");					
		try {
			int i=0;
			for (String line; (line = br.readLine()) != null;) {
				if (line.length() > 6 && line.substring(0, 6).equals("ASSERT")) {
					line = (line.charAt(7) == '(')?line.substring(8):line.substring(7);
					if (line.matches(regex2)) {
						continue;
					}
					if (line.matches(regex0)) {
						String[] ary = p0.split(line);
						if (ary[2].equals("childrenLength")) {
							if (ary[1].equals("<") || ary[1].equals("<=")) {
								ary[4] = ""+ (1+ (new Integer(ary[0])));
							}
							else {
								ary[4] = ary[0];	
							}
							ary[1] = ary[3];
							ary[0] = "childrenLength";
						}
						System.out.println(i++ +" "+ line +" "+ ary[0] +" "+ ary.length);
						switch(ary[0]) {
						case("parent"):
							setParent(ary[3], ary[1], -2);
							break;
						case("child"):
							setParent(ary[1], ary[3], -2);
							break;
						case("childIndex"):
							//getNode(ary[1]).setPosition(new Integer(ary[5]));
						    break;
						case("children"):
							setParent(ary[1], ary[3], new Integer(ary[5]));
							break;
						case("childrenLength"):
							System.out.println("childrenLength "+ ary[1] +" "+ ary[4]);
							try {
								getNode(ary[1]).setChildrenLength(new Integer(ary[4]));
							}
							catch(Exception e) {
								
							}
							break;
						case("firstChild"):
							setParent(ary[1], ary[3], 0);
							break;
						case("lastChild"):
							setParent(ary[1], ary[3], -1);
							break;
						case ("nextSibling"):
							setSibling(ary[3], ary[1]);
							break;																
						case ("previousSibling"):
							setSibling(ary[1], ary[3]);
							break;
						case("root"):
							setRoot(ary[1]);					
							break;
						}
						
					}
					/*else if (relation.matches(regex1)) {
						String[] ary = p1.split(relation);
						System.out.println(i++ +" "+ relation +" "+ ary.length);
					}*/
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
			Set<CVCnode> branches = new HashSet<CVCnode>();
			Iterator<CVCnode> itr_cvc = nameToNode.values().iterator();
			while (itr_cvc.hasNext()) {
				CVCnode node = itr_cvc.next();
				if (node.getParent() == null) {					
					if (node.aliases.contains("r")) {
						if (root instanceof CVCnode) {
							root.merge(node);
						}
						else {
							root = node;
						}
					}
					else {
						branches.add(node);
					}
				}
			}
			branches.remove(root);
			Iterator<CVCnode> itr_lv1 = root.children.iterator();
			itr_cvc = branches.iterator();
			while (itr_lv1.hasNext()) {
				CVCnode child = itr_lv1.next();
				if (child.getAttribute("id") == null && itr_cvc.hasNext()) {
					child.merge(itr_cvc.next());
				}
			}
			while(itr_cvc.hasNext()) {
				CVCnode branch = itr_cvc.next();
				branch.setPosition(root.children.size());
				branch.setParent(root);
			}
			Element rootElem = root.toDOM(document);
			document.appendChild(rootElem);
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
				System.out.println(itr_cvc.next().getAliases());
			}
		} 
		catch (FileNotFoundException e) {
			e.printStackTrace();
		}			
	}
}
