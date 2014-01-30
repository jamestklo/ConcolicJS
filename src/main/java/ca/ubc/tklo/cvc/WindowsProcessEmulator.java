package ca.ubc.tklo.cvc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.List;

public abstract class WindowsProcessEmulator  {
    protected Process process;
    protected BufferedWriter out;
    protected BufferedReader input;
    
    public String process(String str) {
		try {
			out.write(str);
			out.newLine();
			out.flush();
			
    		String line;
			StringBuffer pipe = new StringBuffer();
    		while((line = input.readLine()) != null && this.isAlive(str, line)) {
        		pipe.append(line);
        		pipe.append(System.lineSeparator());
        	}
			return pipe.toString();
		} 
		catch (Exception e) {
			e.printStackTrace();
		}		
		return null;
    }
    public void quit() {
    	try {
			out.close();
	    	input.close();
		} 
    	catch (IOException e) {
			e.printStackTrace();
		}
    	process.destroy();
    }
    
    abstract protected boolean isAlive(String str, String line);
    public WindowsProcessEmulator (String command) {
    	try {
			process = Runtime.getRuntime().exec(command);
			initialize();
		} 
    	catch (IOException e) {
			e.printStackTrace();
		}    	
    }
    public WindowsProcessEmulator(List<String> commands) {
    	try {
			process = (new ProcessBuilder(commands)).start();
			initialize();
		} 
    	catch (IOException e) {
			e.printStackTrace();
		}    	
    }
    private void initialize() {
		out = new BufferedWriter (new OutputStreamWriter(process.getOutputStream()));
		input =  new BufferedReader (new InputStreamReader(process.getInputStream()));
    }    
}
