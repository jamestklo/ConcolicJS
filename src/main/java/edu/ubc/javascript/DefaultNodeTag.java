package edu.ubc.javascript;

import com.google.javascript.rhino.Node;

public class DefaultNodeTag<T> implements NodeTag<T> {

	private Node node;
	private String name;
	private T value;
	
	public DefaultNodeTag(Node node, String name, T value) {
		this.node = node;
		this.name = name;
		this.value = value;
	}
	
	@Override
	public Node getNode() {
		return node;
	}

	@Override
	public void setNode(Node node) {
		this.node = node;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public T getValue() {
		return value;
	}

	@Override
	public void setName(String name) {
		this.name = name;
	}

	@Override
	public void setValue(T value) {
		this.value = value;
	}
	
	public String toString() {
		return "{name:"+name+", value:"+value.toString()+"}";
	}

}
