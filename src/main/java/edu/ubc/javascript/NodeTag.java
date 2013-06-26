package edu.ubc.javascript;

import com.google.javascript.rhino.Node;

public interface NodeTag<T> extends Tag<T> {
	
	public Node getNode();
	public void setNode(Node node);
	
}
