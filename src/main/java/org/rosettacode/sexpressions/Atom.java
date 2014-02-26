package org.rosettacode.sexpressions;

import org.rosettacode.sexpressions.LispParser.Expr;
 
public class Atom implements Expr
{
    String name;
    public String toString()
    {
        return name;
    }
    public Atom(String text)
    {
        name = text;
    }
}
