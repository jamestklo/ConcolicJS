package ca.ubc.tklo.smt2;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.rosettacode.sexpressions.Atom;
import org.rosettacode.sexpressions.ExprList;
import org.rosettacode.sexpressions.ExprTraverser;
import org.rosettacode.sexpressions.ExprVisitor;
import org.rosettacode.sexpressions.LispParser;
import org.rosettacode.sexpressions.LispTokenizer;
import org.rosettacode.sexpressions.StringAtom;
import org.rosettacode.sexpressions.LispParser.Expr;
import org.rosettacode.sexpressions.LispParser.ParseException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.google.common.base.Joiner;


public class Smt2Cvc4Parser {
	String sessionID = null;
	int lengthID = 0;
	Map<String, Smt2Node> nodes = null;
	public Smt2Cvc4Parser(BufferedReader br, ListIterator<PatternParser> itr_parser) {
		nodes = new HashMap<String, Smt2Node>();
		parse(br, itr_parser);
	}
	
	static public abstract class PatternParser {
		final String pattern;
		final int length;
		public PatternParser(String pattern) {
			this.pattern = pattern;
			this.length = pattern.length();
		}
		boolean isReady(String line) {
			return (line.length() > length && line.indexOf(pattern) == 0); 
		}
		abstract void parse(String line, BufferedReader br, Smt2Cvc4Parser scp);
	}
	
	static public class SessionParser extends PatternParser  {
		public SessionParser() {
			super("(define-fun sessionID () String type \"");
		}

		@Override
		void parse(String line, BufferedReader br, Smt2Cvc4Parser scp) {
			scp.sessionID = line.substring(length, line.length()-2);
			scp.lengthID = scp.sessionID.length();
			//System.out.println("sessionID="+ scp.sessionID);
		}
	}
	static public class CardinalityParser extends PatternParser {
		static final String pattern_node	= "; rep: ";
		static final int 	length_node		= pattern_node.length();
		public CardinalityParser() {
			super("; cardinality of Node is ");
		}
		
		@Override
		public void parse(String line, BufferedReader br, Smt2Cvc4Parser scp) {
			int cardinality = Integer.parseInt(line.substring(length));
			Map<String, Smt2Node> nodes = scp.nodes;
			try {
				br.readLine(); // skip a line
				System.out.println("cardinality="+ cardinality);
				for (int i=0; i < cardinality; ++i) {
					line = br.readLine();
					String name = line.substring(length_node);
					Smt2Node node = new Smt2Node();
					nodes.put(name, node);	
					System.out.println("\""+ name +"\" "+ node);
				}
			}
			catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	static public abstract class SetterParser extends PatternParser implements ExprVisitor {
		Smt2Cvc4Parser scp;
		int wait = -2;
		String active = null;

		public SetterParser(String pattern) {
			super(pattern);
		}
		
		@Override
		void parse(String line, BufferedReader br, Smt2Cvc4Parser scp) {
			this.scp = scp;
			ExprTraverser et = new ExprTraverser(this);
			et.depthFirst(ExprTraverser.parse(line));
			scp = null;
			wait = -2;
			active = null;
		}
		
		@Override
		public void visit(Expr expr) {
			String current = null;
			if (expr instanceof StringAtom) {
				current = ((StringAtom) expr).getValue();
			}
			else if (expr instanceof Atom) {
				current = ((Atom) expr).toString();
			}
			if (current != null) { 
				switch(current) {
				case("ite"): wait = 3; return;
				}
				switch (wait--) {
				case 2:
					active = current;
					break;
				case 0:				
					this.set(active, current);
					break;
				case -1:
					Set<String> keys = scp.nodes.keySet();
					Iterator<String> iterator = keys.iterator();
					while (iterator.hasNext()) {
						String key = iterator.next();
						//System.out.println(key +" set "+ current);
						this.set(key, current);
					}
					break;
				}
			}			
		}
		abstract boolean set(String key, String value);
	}
	
	static public class PositionParser extends SetterParser {
		public PositionParser() {
			super("(define-fun position ");
		}

		@Override
		public boolean set(String key, String current) {
			Smt2Node node = scp.nodes.get(key);
			if (node.position == -1) {
				int position = Integer.parseInt(current);
				node.position = position;
				System.out.println(key +" position "+ position);
				return true;
			}
			return false;
		}
	}
	
	static public class LengthParser extends SetterParser {
		public LengthParser() {
			super("(define-fun length ");
		}
		
		@Override
		public boolean set(String key, String current) {
			Smt2Node node = scp.nodes.get(key);
			if (node.length == -1) {
				System.out.println(key +" length "+ current);
				node.length = Integer.parseInt(current);
				return true;
			}
			return false;
		}
	}
	
	static public class ParentParser extends SetterParser {	
		public ParentParser() {
			super("(define-fun parentAlias ");
		}
		
		@Override
		boolean set(String key, String value) {
			Smt2Node node = scp.nodes.get(key);
			if (node.parent == null && node.position > 0) {
				node.parent = scp.nodes.get(value);
				System.out.println(key +" "+ node.position +" parent "+ value);
				return true;
			}
			return false;
		}
	}
	
	static public class IdParser extends SetterParser {
		public IdParser() {
			super("(define-fun id ");
		}
		
		@Override
		boolean set(String key, String value) {
			if (value == null) {
				return false;
			}			
			Smt2Node node = scp.nodes.get(key);
			String old = node.id;
			if (old != null || value.equals(old)) {
				return false;
			}			
			value = (value.indexOf(scp.sessionID) == 0)?value.substring(scp.lengthID):"";
			System.out.println(key +" id "+ value);
			node.id = value;
			return true;
		}
	}

	static public class TagParser extends SetterParser {
		public TagParser() {
			super("(define-fun tag ");
		}
		@Override
		boolean set(String key, String value) {
			if (value == null || value.equals("")) {
				return false;
			}
			
			Smt2Node node = scp.nodes.get(key);
			String old = node.tag;
			if (old != null || value.equals(old)) {
				return false;
			}
			value = (value.indexOf(scp.sessionID) == 0)?value.substring(scp.lengthID):"";
			System.out.println(key +" tagName "+ value);
			node.tag = value;
			return true;
		}
	}
		
	static public abstract class ArrayParser extends PatternParser implements ExprVisitor {
		
		Smt2Cvc4Parser scp = null;
		
		public ArrayParser(String pattern) {
			super(pattern);
		}

		@Override
		void parse(String line, BufferedReader br, Smt2Cvc4Parser scp) {
			this.scp = scp;
			ExprTraverser et = new ExprTraverser(this);
			touched = new HashSet<String>();
			et.depthFirst(ExprTraverser.parse(line));
			scp = null;
			active = null;
			previous = null;
			touched = null;
		}
		
		Set<String> touched = null;
		String active = null;
		String previous = null;
		@Override
		public void visit(Expr expr) {
			if (expr instanceof StringAtom) {
				String current = ((StringAtom) expr).getValue();
				//System.out.println(expr.toString() +" "+ previous +" "+ active);
				if (active == null) {
					active = "";
				}
				else if (isMatch(previous, current)) {
					if (active.equals("")) {
						Iterator<String> itr_name = scp.nodes.keySet().iterator();
						while (itr_name.hasNext()) {
							String key = itr_name.next();
							if (! touched.contains(key)) {
								set(key, previous, current);
							}
						}
					}
					else {
						set(active, previous, current);
					}	
				}
				previous = current;
			}
			else if (expr instanceof Atom) {
				String current = ((Atom) expr).toString();
				//System.out.println(current +" "+ previous +" "+ active);
				if (current.equals("ite")) {
					previous = current;
				}
				else if (previous == null) {
					return;
				}
				else if (previous.equals("ite")) {
					previous = current;
				}
				else if (previous.equals("=")) {
					active = current;
					touched.add(active);
					previous = null;
				}
				else {
					active = null;
				}
			}
		}
		
		abstract boolean isMatch(String key, String value);
		abstract boolean set(String name, String key, String value);
	}
	
	static public class ClassParser extends ArrayParser {
		public ClassParser() {
			super("(define-fun className ");
		}

		@Override
		boolean set(String name, String key, String value) {
			System.out.println(name +" className "+ value);
			scp.nodes.get(name).addClass(value);
			return true;
		}

		@Override
		boolean isMatch(String key, String value) {	
			return (key == null || key.equals(" ") || value == null || value.equals(" ") || value.equals(""))?
					false:
					(key.indexOf(scp.sessionID) == 0 && value.equals(key.substring(scp.lengthID)));
		}
	}
	
	static public class AttributeParser extends ArrayParser {

		public AttributeParser() {
			super("(define-fun attribute ");
		}

		@Override
		boolean isMatch(String key, String value) {
			return (key != null && key.indexOf("sessionID") == 0);
		}

		@Override
		boolean set(String name, String key, String value) {
			key = key.substring(scp.lengthID);
			if (key.equals(value)) {
				return false;
			}
			System.out.println(name +" attribute "+ key +" "+ value);
			scp.nodes.get(name).addAttribute(key, value);
			return true;
		}
	}
	private void parse(BufferedReader br, ListIterator<PatternParser> itr_parser) {
		PatternParser parser = null;
		if (itr_parser.hasNext()) {
			parser = itr_parser.next();
		}
		else {
			return;
		}
		String line;
		try {
			while ((line = br.readLine()) != null) {
				if (parser.isReady(line)) {
					parser.parse(line, br, this);
					if (itr_parser.hasNext()) {
						parser = itr_parser.next();
					}
					else {
						break;
					}
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	Document document = null;
	String defaultTag = null;
	Map<Smt2Node, Map<Integer, Smt2Node>> childrens = null;
	Document toDOM(String defaultTag) {
		this.defaultTag = defaultTag;
		Set<Smt2Node> roots = new HashSet<Smt2Node>();
		childrens = new HashMap<Smt2Node, Map<Integer, Smt2Node>>();
		Iterator<String> itr_str = nodes.keySet().iterator();
		while (itr_str.hasNext()) {
			Smt2Node node = nodes.get(itr_str.next());
			if (node.position == 0) {
				roots.add(node);
				//System.out.println("root "+ node);
			}
			else {
				Smt2Node parent = node.parent;
				Map<Integer, Smt2Node> children = childrens.get(parent);
				if (children == null) {
					children = new HashMap<Integer, Smt2Node>();
					childrens.put(parent, children);
					//System.out.println(node +" "+ parent +" "+ children);
				}
				children.put(node.position, node);
			}
		}
		
		Iterator<Smt2Node> itr_node = roots.iterator();
		Document doc = null;
		try {
			doc = this.document = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
			while (itr_node.hasNext()) {
				document.appendChild(createElement(itr_node.next()));
				
			}
		} 
		catch (ParserConfigurationException e) {
			e.printStackTrace();
		}
		finally {
			this.document = null;
			this.defaultTag = null;
			this.childrens = null;
		}
		return doc;
	}
	
	private String calTag(Smt2Node parent) {
		return defaultTag;
	}
	
	private Element createElement(Smt2Node node) {
		String str = node.tag;
		Element element = document.createElement(str.equals("")?calTag(node.parent):str);
		Iterator<String> itr_str = node.attributes.keySet().iterator();
		
		str = node.id;
		if (! str.equals("")) {
			element.setAttribute("id", str);
		}
		while (itr_str.hasNext()) {
			String key = itr_str.next();
			String value = node.attributes.get(key);
			element.setAttribute(key, value);
		}		
		if (element.hasAttribute("class")) {
			node.classNames.add(element.getAttribute("class"));
		}
		if (node.classNames.size() > 0) {
			element.setAttribute("class", Joiner.on(" ").join(node.classNames));
		}
				
		Map<Integer, Smt2Node> children = childrens.get(node);
		int length = node.length;
		for (int i=1; i <= length; ++i) {
			Smt2Node child = children.get(i);
			if (child == null) {
				element.appendChild(document.createElement(calTag(node)));
			}
			else {
				element.appendChild(createElement(child));
			}
		}
		System.out.println(node +" "+ element);
		return element;
	}
	
	public static void outXML(Document document, OutputStream out) {
		try {
			//XML specific representation output (exact details not relevant)
			TransformerFactory tf = TransformerFactory.newInstance();
			Transformer transformer = tf.newTransformer();
			transformer.transform(new DOMSource(document), new StreamResult(out));
		}
		catch(Exception e) {
			throw new RuntimeException(e);
		}
	}
	
	public static void main (String[] args) {
		try {
			BufferedReader br = new BufferedReader(new FileReader("/Users/tklo/git/ConcolicJs/smt/cvc4-out1a.smt2"));
			//BufferedReader br = new BufferedReader(new FileReader("Z:/git/ConcolicJs/smt/cvc4-out1a.smt2"));
			ArrayList<PatternParser> parsers = new ArrayList<PatternParser>();
			parsers.add(new SessionParser());
			parsers.add(new CardinalityParser());
			parsers.add(new PositionParser());
			parsers.add(new LengthParser());
			parsers.add(new IdParser());
			parsers.add(new TagParser());			
			parsers.add(new ParentParser());
			//parsers.add(new ClassParser());
			parsers.add(new AttributeParser());
			Smt2Cvc4Parser smp = new Smt2Cvc4Parser(br, parsers.listIterator());
			Document document = smp.toDOM("a");
			Smt2Cvc4Parser.outXML(document, System.out);
		} 
		catch (IOException e) {
			e.printStackTrace();
		}
	}
}
