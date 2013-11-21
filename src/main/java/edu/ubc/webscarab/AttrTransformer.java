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
		process(node);
		Iterator<Node> itr_node = node.childNodes().listIterator();
		while (itr_node.hasNext()) {
			visit(itr_node.next());
		}		
	}
	
	private void process(Node node) {
		Iterator<Attribute> itr_attr = node.attributes().iterator();
		while (itr_attr.hasNext()) {
			Attribute attr = itr_attr.next();
			String key = attr.getKey();
			int klen = key.length();
			String val = attr.getValue();
			int vlen = val.length();
			try {
				if (klen > 2 && key.substring(0, 2).equals("on") && vlen > 0) {
					if (val.contains("return")) {
						String[] stmts = val.split(";");
						StringBuffer sb = new StringBuffer();
						int l = stmts.length;
						for (int i=0; i < l; ++i) {
							String stmt = stmts[i];
							if (stmt.contains("return")) {
								sb.append(stmt+"; ");
							}
							else {
								sb.append(transformer.transform(new StringReader(stmt)));
							}
						}
						val = sb.toString();						
					}
					else {
						val = transformer.transform(new StringReader(val));
					}
					attr.setValue(val.replace("\n", " "));
				}
				else if (vlen > 11 && val.substring(0, 11).equals("javascript:")) {
					attr.setValue( "javascript:"+ transformer.transform(new StringReader(val.substring(11))).replace("\n", " ") );
				}
			}
			catch (IOException e) {				
				e.printStackTrace();
			}
		}
		if (node.nodeName().equals("script")) {
			System.out.println(node.attr("text"));
			System.out.println(node.outerHtml());
		}
	}
}
