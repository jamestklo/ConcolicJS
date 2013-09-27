package ca.ubc.salt.concolicjs;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.google.common.base.Joiner;

// point lmusolver.jar to build-path
import fr.inrialpes.wam.treelogic.BottomUpSolver.FiniteTreeSolver;
import fr.inrialpes.wam.treelogic.BottomUpSolver.FormulaSolver;

public class ApiSolver {

	/*
	 * how to make solver to generate valid HTML?
	 * how to generate elements with attributes?  attributes or text that satsify constraints: HAMPI/Kaluzza
	 */
	public static String[] test1() {
		//http://www.w3schools.com/xpath/xpath_syntax.asp
		ArrayList<String> ary = new ArrayList<String>();		
		/*
		ary.add("nodename");
		ary.add("/");
		ary.add("//");
		ary.add(".");
		ary.add("..");
		ary.add("@");
		
		ary.add("bookstore");
		ary.add("/bookstore");
		ary.add("bookstore/book");
		ary.add("//book");
		ary.add("bookstore//book");
		ary.add("//@lang");
		
		ary.add("/bookstore/book[1]");
		ary.add("/bookstore/book[last()]");
		ary.add("/bookstore/book[last()-1]");
		ary.add("/bookstore/book[position()<3]");
		ary.add("//title[@lang]");
		ary.add("//title[@lang='eng']");
		*/
		//ary.add("/bookstore/book[./price=\"35.00\"]");
		//ary.add("/bookstore/book[./price=35.00]/title");
		//ary.add("/bookstore/book[@__0=1][@price][@innerHTML][@title]/title");
		//ary.add("nt[preceding-sibling::a[preceding-sibling::b]]");
		//ary.add("/node[parent::p]/*[following-sibling::*[following-sibling::*[following-sibling::*]]]");
		ary.add("a[@id=\"1\"]");
		/*
		ary.add("*");
		ary.add("@*");
		ary.add("node()");
		
		ary.add("/bookstore/*");
		ary.add("//*");
		ary.add("//title[@*]");
		
		ary.add("//book/title | //book/price");
		ary.add("//title | //price");
		ary.add("/bookstore/book/title | //price");
		*/
		return ary.toArray(new String[0]);
	}
	
	public static String count1(String nt) {		
		return nt +"[not(following::"+ nt +") and not(preceding::"+ nt +") and not(ancestor::"+ nt +") and not(descendant::"+ nt +")]";
	}
	public static String firstChild(String domF) {		
		return "child::"+ domF +"[not(preceding-sibling::*)]";
	}
	public static String lastChild(String domL) {		
		return "child::"+ domL +"[not(following-sibling::*)]";		
	}
	public static String childlen(String dom, int len) {
		String left="", right="*]";		
		// children=1 select("dom[child::*]")
		// childlen=2 select("dom[child::*[preceding-sibling::*]]")
		// childlen=3 select("dom[child::*[preceding-sibling::*[preceding-sibling::*]]]")
		for (int i=len; i-- > 1;) {
			left 	+= "*[preceding-sibling::";
			right	+= "]";
		}
		return dom+"[child::"+ left + right;
	}
	public static String select(String xpath) {
		return "select(\""+ xpath +"\")";
	}	
	public static String html(String xpath, String[] nodes) {
		String query=xpath;		
		for (int i=nodes.length; i-- > 0;) {
			String node = nodes[i];
			query = query.replace(node+"[", "descendant::"+node+"[").replace("::descendant::", "::");
		}
		return "/html["+ query +"\t]";		
	}
	
	public static void main(String[] args) {
		/*
		ArrayList<String> als = new ArrayList<String>();
		String dom[] = {"dom0", "dom1", "domC"};
		for (int i=dom.length; i-- > 0;) {
			als.add(count1(dom[i]));
		}
		als.add("dom0["+ firstChild("domC") +"] | dom1["+ lastChild("domC") +"]");
		als.add("dom0[parent::domC] | dom1[parent::domC]");
		als.add(childlen("dom0", 3));
		als.add(childlen("dom1", 2));
		
		String ary[] = als.toArray(new String[0]);
		for (int i=ary.length; i-- > 0;) {
			ary[i] = select(html(ary[i], dom));
		}
		
		String a = Joiner.on(" &\n").join(ary);
		System.out.println(a);
		api_solve(a);		
		*/
		String str = "select(\"/html[descendant::dom1[child::domC[not(following-sibling::*)]]]\") &"
		+"select(\"/html[descendant::dom1[following-sibling::*[parent::dom2 and not(following-sibling::*)]]]\") &"
		+"select(\"/html[descendant::dom0[parent::domC] | descendant::dom1[parent::domC]]\") &"
		+"select(\"/html[descendant::dom2[not(following::dom2) and not(preceding::dom2) and not(ancestor::dom2) and not(descendant::dom2)]]\") &"
		+"select(\"/html[descendant::domC[not(following::domC) and not(preceding::domC) and not(ancestor::domC) and not(descendant::domC)]]\") &"
		+"select(\"/html[descendant::dom1[not(following::dom1) and not(preceding::dom1) and not(ancestor::dom1) and not(descendant::dom1)]]\") &"
		+"select(\"/html[descendant::dom0[not(following::dom0) and not(preceding::dom0) and not(ancestor::dom0) and not(descendant::dom0)]]\")";
		api_solve(str);
	}
	
	/*
	 * returns null string if formula is unsatisfiable
	 */
	private static String api_solve(String str) {
		boolean is_attributes = false;
		boolean is_printtypes = false;
		boolean is_stats = false;
		boolean is_printFormula = false;
		boolean is_printLean = false;
		boolean is_compressNames = false;

		PrintStream out = System.out;
		FormulaSolver formulaSolver = new FormulaSolver();
		FiniteTreeSolver solver = formulaSolver.solve_formula(str, is_attributes, is_printtypes, is_stats, is_printFormula, is_printLean, is_compressNames, out);
		return solver.getsatisfyingexample();
	}
}
