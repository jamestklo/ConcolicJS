package ca.ubc.tklo.smt2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class Smt2Node {
	Smt2Node parent = null;
	int position = -1;
	int length = -1;

	String id = null;
	String tag = null;
	Set<String> classNames = new HashSet<String>();
	Map<String, String> attributes = new HashMap<String, String>();
	boolean addClass(String classname) {
		return classNames.add(classname);
	}
	Object addAttribute(String key, String value) {
		return attributes.put(key, value);
	}
}
