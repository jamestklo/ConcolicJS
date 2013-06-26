package edu.ubc.javascript;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.Map;

import com.google.javascript.rhino.Node;

public class TagManager {

	private static Map<Object, TagMap> map = new IdentityHashMap<Object, TagMap>();
	
	public static class TagList extends LinkedList<Tag> {}
	private static class TagMap extends HashMap<String, TagList> {}
		
	public static TagList getTags(Object obj, String name) {
		TagMap tagMap = map.get(obj);
		if(tagMap == null) {
			return new TagList();
		} 
		else {
			TagList list = tagMap.get(name);
			if(list != null) {
				return list;
			} 
			else {
				return new TagList();
			}
		}
	}
	
	public static Tag getUniqueTag(Object obj, String name) {
		TagMap tagMap = map.get(obj);
		if(tagMap == null) {
			return null;
		} else {
			TagList list = tagMap.get(name);
			if(list == null) {
				return null;
			} else {
				return list.getFirst();
			} 
		}
	}
	
	public static void tagNode(Node node, String name, Object value) {
		NodeTag tag = new DefaultNodeTag(node, name, value);
		addTag(node, name, tag);
	}
		
	private static void addTag(Object obj, String name, Tag tag) {
		TagMap tagMap = map.get(obj);
		if(tagMap == null) {
			tagMap = new TagMap();
			map.put(obj, tagMap);
		} 
		TagList list = tagMap.get(name);
		if(list == null) {
			list = new TagList();
			tagMap.put(name, list);
		}
		list.add(tag);
	}
}
