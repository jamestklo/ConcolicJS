package ca.ubc.salt.concolicjs;

import java.io.PrintStream;

import fr.inrialpes.wam.treelogic.BottomUpSolver.FiniteTreeSolver;
import fr.inrialpes.wam.treelogic.BottomUpSolver.FormulaSolver;

public class ApiSolver {

	public static void main(String[] args) {
		String str = "select(\"a/b[following-sibling::c/parent::d]\")";
		System.out.println(api_solve(str));
		// this XML can be parsed
	}
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
