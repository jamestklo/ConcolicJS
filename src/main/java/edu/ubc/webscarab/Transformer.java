package edu.ubc.webscarab;

import java.io.IOException;

public interface Transformer {
	public String transform(String filename, String input) throws IOException;
}
