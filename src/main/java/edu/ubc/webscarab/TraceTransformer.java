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
		if (filename.indexOf("genoverse")>=0) {
			code = code.replaceAll("char\\s+", "char2");
			code = code.replaceAll("char;", "char2;");			
			code = code.replaceAll("\\.new", ".new2");
			code = code.replaceAll("new\\s+:", "new2 :");	
			code = code.replaceAll("\\.default;"	, ".default2;");
			code = code.replaceAll("\\.default\\."	, ".default2.");
			code = code.replaceAll("\\.default\\s+"	, ".default2");
		}
		
		// temp fix for Tudu
		String dwr=null, dwrInsert=null, dwrReply=null;
		code = code.replaceAll("throw 'allowScriptTagRemoting is false.';", "");
		if (code.contains("//#DWR")) {
			dwr = "//#DWR";			
		}
		if (code.contains("//#DWR-INSERT")) {
			dwrInsert = "//#DWR-INSERT";
		}
		if (code.contains("//#DWR-REPLY")) {
			dwrReply = "//#DWR-REPLY";
		}
			
		code = code.replaceAll(",\\s+}", "}").replaceAll(",\\s+]", "]");						
		String output = transform(SourceFile.fromCode(filename, code)).replaceAll("0.0 === self.FileError", "void 0 === self.FileError");
		
		if (dwr != null) {
			output = dwr +"\n"+ output;
		}
		if (dwrInsert != null) {
			output = dwrInsert +"\n"+ output;
		}
		if (dwrReply != null) {
			output = dwrReply +"\n"+ output;
		}
		
		return output + "\n/*TraceTransformer:"+ filename +"*/\n";
	}
	
	public static void main (String[] args) {
		String code = new String("start_code();\n"
					+"/* First comment */\n"
					+"more_code();\n" 
					+"/* Second comment */\n"
					+"end_code();\n");
		System.out.println(code.replaceAll("(?:/\\*(?:[^*]|(?:\\*+[^*/]))*\\*+/)|(?://.*)",""));
		System.out.println("\n");
	}
}
