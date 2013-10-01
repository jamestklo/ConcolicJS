package ca.ubc.salt.concolicjs;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
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

public class XMLgenerator {
	
	Map<String, CVCnode> nameToNode = new HashMap<String, CVCnode>();
	public XMLgenerator(String filepath) {
		parseLogs(filepath);
	}
	
	CVCnode getAlias(String name) {
		CVCnode ret = nameToNode.get(name);
		if (ret == null) {
		  ret = new CVCnode(nameToNode);
		  ret.addName(name);
		  nameToNode.put(name, ret);
		}
		return ret; 
	}
	
	CVCnode setParent(String child, String parent) {		
		CVCnode childNode = getAlias(child);
		CVCnode parentNode = childNode.parent;
		if (nameToNode.get(parent) == null && parentNode != null) {
			parentNode.addName(parent);
			nameToNode.put(parent, parentNode);
			return childNode;
		}
		return setParent(child, getAlias(parent));
	}
	
	CVCnode setParent(String child, CVCnode parent) {
		CVCnode childNode = getAlias(child);
		childNode.setParent(parent);
		return childNode;
	}
	
	void parseLogs(String filepath) {		
		try {
			BufferedReader br = new BufferedReader(new FileReader(filepath));
			String line;

			String regex0 = "(parent|children|firstChild|lastChild|following_sibling|preceding_sibling).*";
			Pattern p0 = Pattern.compile("[\\(,\\s\\)]");

			String regex1 = "\\(.* = .*\\);$";
			Pattern p1 = Pattern.compile("[\\(\\s=\\)]");			

			int i = 0;
			while ((line = br.readLine()) != null) {
				if (line.length() > 6 && line.substring(0, 6).equals("ASSERT")) {					
					String relation = line.substring(7);
					if (relation.matches(regex0)) {
						String[] ary = p0.split(relation);
						System.out.println(i++ +" "+ relation +" "+ ary.length);
						if (ary.length > 4) {
							CVCnode childNode;
							switch(ary[0]) {
							case("parent"):
								setParent(ary[3], ary[1]);
								break;
							case("children"):
								childNode = setParent(ary[1], ary[3]);
								childNode.order = new Integer(ary[5]);
								break;
							case("firstChild"):
								childNode = setParent(ary[1], ary[3]);
								childNode.order = 0;						
								break;
							case("lastChild"):
								childNode = setParent(ary[1], ary[3]);
								childNode.order = -1;					
								break;
							case ("preceding_sibling"):
							case ("following_sibling"):
								CVCnode p = new CVCnode(nameToNode);
								setParent(ary[1], p);
								setParent(ary[3], p);								
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
	
	public Document toDOM(Document document) {							
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
			System.out.println(roots.size());
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
	
	static void outXML(Document document, PrintStream out) {
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
	
	public static void main(String[] args) {
		XMLgenerator xmlg = new XMLgenerator("Z:/cvc4/cvc3-output20130913.txt");
		outXML(xmlg.toDOM(null), System.out);
	}
}
