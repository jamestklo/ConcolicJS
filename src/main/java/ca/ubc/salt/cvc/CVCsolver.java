package ca.ubc.salt.cvc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;

// users Java's process builder to abstract using CVC's .exe command line interface
public class CVCsolver {

	public static void main(String[] args) {
		List<String> commandLine = new ArrayList<String>();
		commandLine.add("Z:/cvc4/cvc3-2.4.1-win32-optimized/bin/cvc3.exe");
		commandLine.add("+interactive");
		//commandLine.add("Z:/cvc4/cvc3-example1.cvc");
		ProcessBuilder builder = new ProcessBuilder(commandLine);
		builder.redirectErrorStream(true);			
		builder.redirectInput(ProcessBuilder.Redirect.INHERIT);
		builder.redirectOutput(ProcessBuilder.Redirect.INHERIT);
		//File log = new File("Z:/cvc4/log.txt");
		//builder.redirectOutput(ProcessBuilder.Redirect.appendTo(log));
		try {
			//Process process = builder.start();
			Process process = Runtime.getRuntime().exec( "Z:/cvc4/cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive" );
			OutputStream inputToProcess = process.getOutputStream();
			BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(inputToProcess));			
			writer.write("a, b:INT;\r");
			writer.write("ASSERT a > b AND b > 0;\r");
			writer.write("CHECKSAT;\r");			
			//writer.close();
			
		    InputStream outputOfProcess = process.getInputStream();
		    InputStream error = process.getErrorStream();
		    new StreamCleaner(outputOfProcess).start();
		    new StreamCleaner(error).start();		    
						
		    inputToProcess = process.getOutputStream();
		    writer = new BufferedWriter(new OutputStreamWriter(inputToProcess));
		    writer.write("WHERE;\r");
		    //writer.close();
		    
			process.waitFor();
		} 
		catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private static class StreamCleaner extends Thread {
		private InputStream input;
		public StreamCleaner(InputStream input) {
			this.input = input;
		}
		public void run() {
			byte[] buffer = new byte[512];
			try {
				while (this.input.read(buffer) != -1) {
					System.out.println(new String(buffer));
				}
			}
			catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
