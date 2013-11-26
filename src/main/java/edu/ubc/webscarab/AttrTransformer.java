package edu.ubc.webscarab;

import java.io.IOException;
import java.util.Iterator;
import java.util.ListIterator;

import org.jsoup.Jsoup;
import org.jsoup.nodes.Attribute;
import org.jsoup.nodes.DataNode;
import org.jsoup.nodes.Document;
import org.jsoup.nodes.Node;
import org.jsoup.select.NodeVisitor;

public class AttrTransformer implements Transformer {
	private Transformer transformer;
	
	public AttrTransformer(Transformer rtb) {
		this.transformer = rtb;
	}	
	public String transform(String href, String html) {		
		Document doc = Jsoup.parse(html);
		doc.traverse(new NodeTransformer(href, transformer));
		return doc.html();		
	}
		
	private static class NodeTransformer implements NodeVisitor {
		private Transformer transformer;
		private String href;
		public NodeTransformer(String href, Transformer transformer) {
			this.href = href;
			this.transformer = transformer;
		}

		@Override
		public void head(Node node, int arg1) {
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
									sb.append(transformer.transform(href, stmt));
								}
							}
							val = sb.toString();						
						}
						else {
							val = transformer.transform(href, val);
						}
						attr.setValue(val.replace("\n", " "));
					}
					else if (vlen > 11 && val.substring(0, 11).equals("javascript:")) {
						attr.setValue( "javascript:"+ transformer.transform(href, val.substring(11)).replace("\n", " ") );
					}
				}
				catch (IOException e) {				
					e.printStackTrace();
				}
			}
			String nodename = node.nodeName();
			if (nodename.equals("script")) {
				ListIterator<Node> itr = node.childNodes().listIterator();
				while (itr.hasNext()) {
					Node child = itr.next();
					if (child instanceof DataNode) {
						DataNode datanode = (DataNode) child;
						try {
							datanode.setWholeData(transformer.transform(href, datanode.getWholeData()));
						} 
						catch (IOException e) {
							e.printStackTrace();
						}
					}
				}
			}			
		}

		@Override
		public void tail(Node arg0, int arg1) {			
		}
		
	}
}
