package edu.ubc.javascript;

import java.util.Iterator;

import com.google.common.base.Preconditions;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;

public final class NodeUti1 {
	public static ThreadLocal<String> currentURL 	= new ThreadLocal<String>();
	public static ThreadLocal<String> filename 		= new ThreadLocal<String>();
	public static ThreadLocal<Integer> scriptCount 	= new ThreadLocal<Integer>();
	public static void setURL(String url) {
		currentURL.set(url);
		String split[] = url.split("/");	
		filename.set(split[split.length-1]);
		scriptCount.set(0);
	}	
	
	public static Node detectAncestor(Node n, int[] types) {
		Node detected = null;
		Iterator<Node> itr = n.getAncestors().iterator();
		while (itr.hasNext() && detected == null) {
			detected = itr.next();		
			int dtype = detected.getType();
			int i = -1, t;
			for (i=types.length; i-- > 0;) {
				t = types[i];
				if (t == -1 && NodeUti1.isStatement(detected)) {
					return detected;
				}
				if (t == dtype) {
					return detected;
				}
			}
			detected = null;
		}
		return detected;
	}
	public static boolean isAncestor(Node n, Node ancestor) {
		if (n.equals(ancestor)) {
			return true;
		}		
		Iterator<Node> itr = n.getAncestors().iterator();
		while (itr.hasNext()) {
			if (itr.next().equals(ancestor)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	  * @return Whether the node is used as a statement.
	  */
	static boolean isStatement(Node n) {
	    Node parent = n.getParent();
	    // It is not possible to determine definitely if a node is a statement
	    // or not if it is not part of the AST.  A FUNCTION node can be
	    // either part of an expression or a statement.
	    Preconditions.checkState(parent != null);
	    switch (parent.getType()) {
	      case Token.SCRIPT:
	      case Token.BLOCK:
	      case Token.LABEL:
	        return true;
	      default:
	        return false;
	    }
	}

	  /**
	   * A "simple" operator is one whose children are expressions,
	   * has no direct side-effects (unlike '+='), and has no
	   * conditional aspects (unlike '||').
	   */
	  static boolean isSimpleOperatorType(int type) {
	    switch (type) {
	      case Token.ADD:
	      case Token.BITAND:
	      case Token.BITNOT:
	      case Token.BITOR:
	      case Token.BITXOR:
	      case Token.COMMA:
	      case Token.DIV:
	      case Token.EQ:
	      case Token.GE:
	      case Token.GETELEM:
	      case Token.GETPROP:
	      case Token.GT:
	      case Token.INSTANCEOF:
	      case Token.LE:
	      case Token.LSH:
	      case Token.LT:
	      case Token.MOD:
	      case Token.MUL:
	      case Token.NE:
	      case Token.NOT:
	      case Token.RSH:
	      case Token.SHEQ:
	      case Token.SHNE:
	      case Token.SUB:
	      case Token.TYPEOF:
	      case Token.VOID:
	      case Token.POS:
	      case Token.NEG:
	      case Token.URSH:
	        return true;

	      default:
	        return false;
	    }
	  }	  
}
