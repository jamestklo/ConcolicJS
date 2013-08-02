package ca.ubc.salt.concolicjs;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

// point lmusolver.jar to build-path
import fr.inrialpes.wam.treelogic.BottomUpSolver.FiniteTreeSolver;
import fr.inrialpes.wam.treelogic.BottomUpSolver.FormulaSolver;

public class ApiSolver {

	/*
	 * how to make solver to generate valid HTML?
	 * how to generate elements with attributes?  attriutes or text that satsify constraints: HAMPI/Kaluzza
	 */
	public static String[] test1() {
		//http://www.w3schools.com/xpath/xpath_syntax.asp
		String ary[] = new String[64];
		int i=0;
		/*
		ary[i++] = "nodename";
		ary[i++] = "/";
		ary[i++] = "//";
		ary[i++] = ".";
		ary[i++] = "..";
		ary[i++] = "@";
		
		ary[i++] = "bookstore";
		ary[i++] = "/bookstore";
		ary[i++] = "bookstore/book";
		ary[i++] = "//book";
		ary[i++] = "bookstore//book";
		ary[i++] = "//@lang";
		
		ary[i++] = "/bookstore/book[1]";
		ary[i++] = "/bookstore/book[last()]";
		ary[i++] = "/bookstore/book[last()-1]";
		ary[i++] = "/bookstore/book[position()<3]";
		ary[i++] = "//title[@lang]";
		ary[i++] = "//title[@lang='eng']";
		
		ary[i++] = "/bookstore/book[price=35.00]";
		ary[i++] = "/bookstore/book[price=35.00]/title";
		ary[i++] = "/bookstore/book[@price=35.00]/title";
		
		ary[i++] = "*";
		ary[i++] = "@*";
		ary[i++] = "node()";
		
		ary[i++] = "/bookstore/*";
		ary[i++] = "//*";
		ary[i++] = "//title[@*]";
		*/
		ary[i++] = "//book/title | //book/price";
		ary[i++] = "//title | //price";
		ary[i++] = "/bookstore/book/title | //price";
		return ary;
	}
	
	
	public static void main(String[] args) {
		//String str = "select(\"a/b[following-sibling::c/parent::a]\")";
		String ary[] = test1();
		String str="";
		Map<String, String> ans = new HashMap<String, String>();
		int i=0, l=ary.length;
		for (i=0; i < l; i++) {
			try {
				str = "select(\""+ ary[i]+ "\")";
				ans.put(str, api_solve(str));				
			}
			catch (Exception e) {
				System.out.println("test "+ i +" failed: "+ str);
			}
		}
	}
	
	/*
	 * returns null string if formula is unsatisfiable
	 */
	private static String api_solve(String str) {
		boolean is_attributes = true;
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
