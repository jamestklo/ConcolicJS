package org.rosettacode.sexpressions;

import java.util.ListIterator;

import org.rosettacode.sexpressions.LispParser.Expr;
import org.rosettacode.sexpressions.LispParser.ParseException;

public class ExprTraverser {
	ExprVisitor visitor;
	public static Expr parse(String str) {
		LispTokenizer tzr = new LispTokenizer(str);
		LispParser parser = new LispParser(tzr);
		try {
			return parser.parseExpr();
		}
		catch (ParseException e) {
			e.printStackTrace();
		}
		return null;
	}
	public ExprTraverser(ExprVisitor visitor) {
		this.visitor = visitor;
	}
	public void depthFirst(Expr expr) {
		if (expr instanceof ExprList) {
			ListIterator<Expr> li = ((ExprList) expr).listIterator();
			while(li.hasNext()) {
				depthFirst(li.next());
			}
		}
		else {
			visitor.visit(expr);
		}
	}
}
