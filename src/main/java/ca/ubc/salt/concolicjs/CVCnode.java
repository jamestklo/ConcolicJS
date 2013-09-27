package ca.ubc.salt.concolicjs;

import java.util.Set;

public class CVCnode {
	Set<String> aliases;
	CVCnode parent;
	Set<CVCnode> children;
	int order;
	
	public void addName(String name) {
		aliases.add(name);
	}
	
	public void setParent(CVCnode parent, Map<>) {
	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

}
