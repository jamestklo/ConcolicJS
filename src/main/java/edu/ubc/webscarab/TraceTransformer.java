package edu.ubc.webscarab;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import com.google.javascript.jscomp.Compiler;
import com.google.javascript.jscomp.CompilerOptions;
import com.google.javascript.jscomp.NodeTraversal;
import com.google.javascript.jscomp.SourceFile;
import com.google.javascript.jscomp.TraceCondVisitor;
import com.google.javascript.rhino.Node;

import edu.ubc.javascript.ReflectiveNodeTransformer;

public class TraceTransformer implements Transformer {

	public static void main(String[] args) throws Exception {
		TraceTransformer main = new TraceTransformer();
		main.transformAll(new String[] {"U:/public_html/nbpAFZyrx5o/tracing/domtris/tetris.js"});
	}
	
	public void transformAll(String[] args) throws Exception {
		for(String fileName : args) {			
			SourceFile input = SourceFile.fromFile(fileName);
			String output = transform(input);
			PrintWriter pw = new PrintWriter(new OutputStreamWriter(new FileOutputStream(fileName+".out")));
			pw.write(output);
			pw.close();
		}
	}
	
	private String transform(SourceFile input) {
		List<SourceFile> externs = new ArrayList<SourceFile>();
		List<SourceFile> inputs = new ArrayList<SourceFile>();
		CompilerOptions options = new CompilerOptions();
		
		options.setPrettyPrint(true);
		
		inputs.add(input);
		Compiler compiler = new Compiler(System.out);
		compiler.compile(externs, inputs, options);
		
		Node node = compiler.getRoot().getLastChild();		
		NodeTraversal traversal  = null;
		ReflectiveNodeTransformer rnt = new ReflectiveNodeTransformer();

		traversal = new NodeTraversal(compiler, new TraceCondVisitor(compiler, rnt));			
		traversal.traverse(node);

		rnt.commit(false);
		
		return compiler.toSource();
	}
	
	public String transform(String filename, String code) throws IOException {
		return transform(SourceFile.fromCode(filename, code));
	}
}
