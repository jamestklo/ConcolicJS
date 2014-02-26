package org.rosettacode.sexpressions;

import org.rosettacode.sexpressions.LispParser.Expr;

public interface ExprVisitor {
  public void visit(Expr expr);	
}
