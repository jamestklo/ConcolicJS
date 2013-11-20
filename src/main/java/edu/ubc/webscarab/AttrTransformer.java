package edu.ubc.webscarab;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.Iterator;

import org.jsoup.Jsoup;
import org.jsoup.nodes.Attribute;
import org.jsoup.nodes.Document;
import org.jsoup.nodes.Node;

public class AttrTransformer {
	private Transformer transformer;
	
	public AttrTransformer(Transformer rtb) throws FileNotFoundException {
		this.transformer = rtb;
	}
	public String transform(Reader input) {
		BufferedReader br = new BufferedReader(input);
		String line;
		StringBuffer sb = new StringBuffer();
		try {
			while ((line = br.readLine()) != null) {
				sb.append(line);
				sb.append("\n");
			}
		} 
		catch (IOException e) {		
			e.printStackTrace();
		}
		Document doc = Jsoup.parse(sb.toString());
		visit(doc);
		return doc.html();
	}

	private void visit(Node node) {
		Iterator<Attribute> itr_attr = node.attributes().iterator();
		while (itr_attr.hasNext()) {
			Attribute attr = itr_attr.next();
			String key = attr.getKey();
			int klen = key.length();
			String val = attr.getValue();
			int vlen = val.length();
			try {
				if (klen > 2 && key.substring(0, 2).equals("on") && val.length() > 0) {					
					val = transformer.transform(new StringReader(val));
					attr.setValue(val.substring(0, val.length()-1));					
				}
				else if (vlen > 11 && val.substring(0, 11).equals("javascript:")) {
					val = transformer.transform(new StringReader(val.substring(11)));
					attr.setValue("javascript:"+ val.substring(0, val.length()-1));
				}
			}
			catch (IOException e) {
				e.printStackTrace();
			}
		}
		Iterator<Node> itr_node = node.childNodes().listIterator();
		while (itr_node.hasNext()) {
			visit(itr_node.next());
		}
	}
}
