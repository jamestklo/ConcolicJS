package edu.ubc.javascript;

public interface Tag<T> {
	public void setName(String name);
	public String getName();
	public T getValue();
	public void setValue(T value);
}
