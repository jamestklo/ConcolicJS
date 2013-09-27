package ca.ubc.salt.concolicjs;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

public class XMLgenerator {
	Map<String, CVCnode> nameToNode = new HashMap<String, CVCnode>();

	CVCnode getAlias(String name) {
		CVCnode ret = nameToNode.get(name);
		if (ret == null) {
		  ret = new CVCnode();
		  ret.addName(name);
		}
		return ret; 
	}
	
	void setParent(String child, String parent) {
		setParent(getAlias(child), getAlias(parent));
	}
	
	void setParent(CVCnode child, CVCnode parent) {
		Set<String> ret = childToParent.put(child, parent);
		if (ret != null) {	
			parent.addAll(ret);
			Iterator<String> itr_str = ret.iterator();
			while (itr_str.hasNext()) {
				String name = itr_str.next();
				nameToAlias.put(name, parent);				
			}
			Set<String> grandparent = childToParent.get(ret);
			if (grandparent != null) {
				setParent(parent, grandparent);
			}
			
			Set<Set<String>> children = parentToChildren.get(ret);
			if (children != null) {
				Iterator<Set<String>> itr_set = children.iterator();
				while (itr_set.hasNext()) {
					child = itr_set.next();
					childToParent.put(child, parent);
				}
			}
			Set<Set<String>> c1 = parentToChildren.get(parent);
			if (c1 == null) {
				parentToChildren.put(parent,  children);
			}
			else {
				c1.addAll(children);
			}
			parentToChildren.remove(ret);
		}
	}
		
	
	public void parseLogs(String[] args) {		
		try {
						
			BufferedReader br = new BufferedReader(new FileReader("Z:/cvc4/cvc3-output20130913.txt"));
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
							System.out.println(ary[0] +" "+ ary[1] + " "+ ary[3]);													
							switch(ary[0]) {
							case("parent"):
								setParent(ary[3], ary[1]);
								break;
							case("children"):
							case("firstChild"):
							case("lastChild"):
								setParent(ary[1], ary[3]);
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
	public static void main(String[] args) {		
	}
}
