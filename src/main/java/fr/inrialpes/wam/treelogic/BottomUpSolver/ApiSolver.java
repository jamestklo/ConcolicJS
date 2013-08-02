package fr.inrialpes.wam.treelogic.BottomUpSolver;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.Reader;
import java.io.StringReader;

import fr.inrialpes.wam.treelogic.formulas.ElementNameCompressor;
import fr.inrialpes.wam.treelogic.formulas.Formula;
import fr.inrialpes.wam.treelogic.formulas.parser.Lexer;
import fr.inrialpes.wam.treelogic.formulas.parser.parser;
import fr.inrialpes.wam.treelogic.formulas.pool.FormulaPool;
import fr.inrialpes.wam.treelogic.treetype.AttributeExprPostCompilation;

public class ApiSolver {

	public static void main(String[] args) {
		String str = "select(\"a/b[following-sibling::c/parent::d]\")";
		System.out.println(api_solve(str));
	}
	private static String api_solve(String str) {
		boolean is_stats = false;
		boolean is_printLean = false;
		boolean is_printFormula = false;
		boolean is_printtypes = false;
		boolean is_attributes = true;
		boolean is_compressNames = false;
		String log = "";
		PrintStream out = System.out;

		FormulaSolver formulaSolver = new FormulaSolver();
		FiniteTreeSolver solver = formulaSolver.solve_formula(str, is_attributes, is_printtypes, is_stats, is_printFormula, is_printLean, is_compressNames, out);
		return solver.getsatisfyingexample();
	}
}
