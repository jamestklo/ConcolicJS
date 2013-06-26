package edu.ubc.javascript;

import edu.ubc.javascript.TagManager.TagList;

public class Scope {
	
	public static class Local extends Scope {
		private Local() {}
	}
	
	public static class Global extends Scope {
		private Global() {}
	}
	
	public static class Closed extends Scope {
		public int level;
		
		public Closed(int level) {
			this.level = level;
		}
		
		public String getStringReference() {
			String returnValue = "__outer__";
			for(int i=1;i < level; i++) {
				returnValue += ".__outer__";
			}
			return returnValue;
		}
	}
	
	public static Local local = new Local();
	public static Global global = new Global();
	
	public static Scope getScope(Object var) {
		TagList list = TagManager.getTags(var, "scope");
		if((list == null) || (list.size() == 0)) {
			return Scope.local;
		}
		else {
			String value = (String) list.get(0).getValue();
			if(value.equals("local")) {
				return Scope.local;
			} 
			else if(value.equals("global")) {
				return Scope.global;
			} 
			else if(value.startsWith("up")) {
				int level = Integer.parseInt(value.substring(2));
				return new Scope.Closed(level);
			}
		}
		throw new IllegalArgumentException();
	}
	
}
