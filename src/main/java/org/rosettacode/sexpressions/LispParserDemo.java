package org.rosettacode.sexpressions;

import org.rosettacode.sexpressions.LispParser.Expr;
import org.rosettacode.sexpressions.LispParser.ParseException;

public class LispParserDemo
{
    public static void main(String args[])
    {
        //LispTokenizer tzr = new LispTokenizer("((data \"quoted data\" 123 4.5)\n (data (!@# (4.5) \"(more\" \"data)\")))");
        LispTokenizer tzr = new LispTokenizer("(define-fun parentNode (($x1 Node)) Node (ite (= @uc_Node_4 $x1) @uc_Node_3 (ite (= @uc_Node_6 $x1) @uc_Node_5 @uc_Node_0)))");
        LispParser parser = new LispParser(tzr);
 
        try {
            Expr result = parser.parseExpr();
            if (result instanceof Atom) {
            	Atom atom = (Atom) result;
            }
            else if (result instanceof ExprList) {
            	ExprList el = (ExprList) result;
            }
            else if (result instanceof StringAtom) {
            	StringAtom str = (StringAtom) result;
            }
            
            System.out.println(result);
        }
        catch (ParseException e1)
        {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
    }	
}
