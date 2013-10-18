package ca.ubc.salt.cvc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.List;

// users Java's process builder to abstract using CVC's .exe command line interface
public class CVCsolver {
	protected static int counter = 0;	
	protected Process process;
	Thread outputThread;
	Thread inputThread;
	Thread errorThread;	
	protected boolean isRunning = true;
	protected int state = 0;
	public CVCsolver(String command) {
		try {
			
			//process = Runtime.getRuntime().exec( "Z:/cvc4/cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive" );
            ProcessBuilder builder = new ProcessBuilder("cmd");
            builder.redirectErrorStream(true);                        
            builder.redirectInput(ProcessBuilder.Redirect.INHERIT);
            builder.redirectOutput(ProcessBuilder.Redirect.INHERIT);
			process = builder.start();
			/*
			outputThread = new OutputStreamCleaner(this, process.getOutputStream());
			inputThread  = new InputStreamCleaner(this, process.getInputStream());
			errorThread  = new InputStreamCleaner(this, process.getErrorStream());
			
			outputThread.start();
			inputThread.start();
			errorThread.start();
			*/
			process.waitFor();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	public String process(String input) {
		BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
		try {
			writer.write(input);
		} 
		catch (IOException e) {
			e.printStackTrace();
		}
		String output = "";
		return output;
	}
	public void quit() {
	}
	
	public static void main(String[] args) {
		CVCsolver cvcs = new CVCsolver("Z:/cvc4/cvc3-2.4.1-win32-optimized/bin/cvc3.exe");
	}
		
	private static class InputStreamCleaner extends Thread {
		private CVCsolver process;
		private InputStream input;
		public InputStreamCleaner(CVCsolver process, InputStream input) {
			this.process = process;
			this.input = input;
		}
		public void run() {
			BufferedReader reader = new BufferedReader(new InputStreamReader(input));			
			while (process.isRunning) {				
				try {
					String line = reader.readLine();					
					System.out.println(process.state +" "+ counter +" "+ input.available() +" "+ line);
					if (input.available() > 0) {
						process.state = 1;
					}
					else {
						process.state = 2;
					}
					
				}
				catch (IOException e) {
					e.printStackTrace();
				}				
			}
		}
	}
	private static class OutputStreamCleaner extends Thread {
		protected CVCsolver process;
		protected OutputStream output;
		public OutputStreamCleaner(CVCsolver process, OutputStream output) {
			this.process = process;
			this.output = output;
		}
		public void run() {			
			BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(output));
			while (process.isRunning) {
				try {
					if (process.state == 0) {
						writer.write("WHERE;\r");
					}
					else if (process.state == 2) {
						String variable = "a"+counter;
						writer.write(variable +":INT;\n");
						writer.write("ASSERT "+ variable +" = "+ counter +";\n");
						writer.write("QUERY "+ variable +" > 500;\r");
						//writer.write("WHERE;\r");
						++counter;
					}
					output.flush();
				}
				catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
	}
}
