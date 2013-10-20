package ca.ubc.salt.concolicjs;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public abstract class WindowsProcessEmulator  {
    protected Process process;
    protected BufferedWriter out;
    protected BufferedReader input;
    
    public String process(String str) {    	
		try {
			StringBuffer pipe = new StringBuffer();
			out.write(str);
			out.newLine();
			out.flush();
    		String line = "";
    		while((line = input.readLine()) != null && this.isAlive(str, line)) {
        		pipe.append(line);
        		pipe.append("\n");
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
    
    public WindowsProcessEmulator(String command) {
    	Runtime re = Runtime.getRuntime();
    	try {	
    		process = re.exec(command);
    		out = new BufferedWriter (new OutputStreamWriter(process.getOutputStream()));
    		input =  new BufferedReader (new InputStreamReader(process.getInputStream()));
    	}
    	catch (IOException ioe){		
    		ioe.printStackTrace();		
    	}    	
    }            
}
