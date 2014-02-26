package ca.ubc.tklo.smt2;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

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
				//System.out.println("cardinality="+ cardinality);
				for (int i=0; i < cardinality; ++i) {
					line = br.readLine();
					String name = line.substring(length_node);
					//System.out.println("\""+ name +"\"");
					nodes.put(name, new Smt2Node());	
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
						this.set(iterator.next(), current);
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
				//System.out.println(node +" position "+ node.position);
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
				node.length = Integer.parseInt(current);
				return true;
			}
			return false;
		}
	}
	
	static public class ParentParser extends SetterParser {	
		public ParentParser() {
			super("(define-fun parentNode ");
		}
		
		@Override
		boolean set(String key, String value) {
			Smt2Node node = scp.nodes.get(key);
			if (node.parent == null && node.position > 0) {
				node.parent = scp.nodes.get(value);
				//System.out.println(node +" "+ node.position +" parent "+ value);
				return true;
			}
			return false;
		}
	}
	
	static public class IdParser extends SetterParser {
		public IdParser() {
			super("(define-fun idStr ");
		}
		
		@Override
		boolean set(String key, String value) {
			if (value == null || value.equals("")) {
				return false;
			}
			System.out.println(key +" id "+ value);
			return (scp.nodes.get(key).attributes.put("id", value) == null);
		}
	}

	static public class TagParser extends SetterParser {
		public TagParser() {
			super("(define-fun tagName ");
		}
		
		@Override
		boolean set(String key, String value) {
			if (value == null || value.equals("")) {
				return false;
			}
			System.out.println(key +" tagName "+ value);
			Smt2Node node = scp.nodes.get(key);
			if (value.equals(node.tag)) {
				return false;
			}
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
					Set<String> keys = scp.nodes.keySet();
					keys.removeAll(touched);
					touched = keys;
					active = "";
				}
				else if (isMatch(previous, current)) {
					if (active.equals("")) {
						Iterator<String> itr_name = touched.iterator();
						while (itr_name.hasNext()) {
							set(itr_name.next(), previous, current);
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
			super("(define-fun classNode ");
		}

		@Override
		boolean set(String name, String key, String value) {
			if (key.equals(" ")) {
				return false;
			}
			System.out.println(name +" className "+ value);
			scp.nodes.get(name).addClass(value);
			return true;
		}

		@Override
		boolean isMatch(String key, String value) {
			return (value.equals(key) && value.equals("")==false);
			
		}

	}
	
	static public class AttributeParser extends ArrayParser {

		public AttributeParser() {
			super("define-fun attrsNode ");
		}

		@Override
		boolean isMatch(String key, String value) {
			return (value.length() > key.length() && value.indexOf(key) == 0);
		}

		@Override
		boolean set(String name, String key, String value) {
			System.out.println(name +" "+ key +" "+ value);
			return false;
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

	void toDOM(String defaultTag) {
		Set<Smt2Node> roots = new HashSet<Smt2Node>();
		Map<Smt2Node, Map<Integer, Smt2Node>> childrens = new HashMap<Smt2Node, Map<Integer, Smt2Node>>();
		Iterator<String> itr_str = nodes.keySet().iterator();
		while (itr_str.hasNext()) {
			Smt2Node node = nodes.get(itr_str.next());
			if (node.position == 0) {
				roots.add(node);
			}
			else {
				Smt2Node parent = node.parent;
				Map<Integer, Smt2Node> children = childrens.get(parent);
				if (children == null) {
					children = new HashMap<Integer, Smt2Node>();
					childrens.put(parent, children);
				}
				children.put(node.position, node);
			}
		}
		
		Iterator<Smt2Node> itr_node = roots.iterator();
		Set<Element> elements = new HashSet<Element>();
		Document document = null;
		try {
			document = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
			while (itr_node.hasNext()) {
				elements.add(createElement(document, defaultTag, itr_node.next(), childrens));
			}
		} 
		catch (ParserConfigurationException e) {
			e.printStackTrace();
		};
	}
	
	private Element createElement(Document document, String defaultTag, Smt2Node node, Map<Smt2Node, Map<Integer, Smt2Node>> childrens) {
		String tagName = node.tag;
		Element element = document.createElement((tagName instanceof String)?((String) tagName):defaultTag);
		Iterator<String> itr_str = node.attributes.keySet().iterator();
		while (itr_str.hasNext()) {
			String key = itr_str.next();
			element.setAttribute(key, node.attributes.get(key));
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
				element.appendChild(document.createElement(defaultTag));
			}
			else {
				element.appendChild(createElement(document, defaultTag, child, childrens));
			}
		}
		return element;
	}
	
	public static void main (String[] args) {
		try {
			BufferedReader br = new BufferedReader(new FileReader("/Users/tklo/git/ConcolicJs/smt/cvc4-out1a.smt2"));
			ArrayList<PatternParser> parsers = new ArrayList<PatternParser>();
			parsers.add(new CardinalityParser());
			/*parsers.add(new PositionParser());
			parsers.add(new LengthParser());
			parsers.add(new ParentParser());*/
			parsers.add(new IdParser());
			parsers.add(new TagParser());
			parsers.add(new ClassParser());
			Smt2Cvc4Parser smp = new Smt2Cvc4Parser(br, parsers.listIterator());
		} 
		catch (IOException e) {
			e.printStackTrace();
		}
	}
}
