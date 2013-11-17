package ca.ubc.tklo.cvc;

import java.util.HashMap;
import java.util.Map;

public class ExperimentTrial {
	public static void main(String[] args) {
		Map<Character, Integer> counts = new HashMap<Character, Integer>();		
		Character c0 = new Character('c');
		counts.put(c0, 100);
		Character c1 = new Character('c');
		System.out.println(counts.get(c1));
	}
}
