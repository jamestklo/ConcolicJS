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
    		Thread thread = new InputCleaner(this, pipe);
    		thread.start();
    		while (thread.isAlive());
			return pipe.toString();
		} 
		catch (Exception e) {
			e.printStackTrace();
		}				   
		return null;
    }
    public void quit() {
    	process.destroy();
    }
    
    abstract protected boolean isAlive(String line);
    
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
        
    private static class InputCleaner extends Thread {
    	WindowsProcessEmulator wpe;    	
    	protected StringBuffer pipe;
    	public InputCleaner(WindowsProcessEmulator wpe, StringBuffer pipe) {
    		this.wpe = wpe;
    		this.pipe = pipe;
    	}
    	public void run() {    		
        	String line;
        	BufferedReader input = wpe.input;
        	try {
            	while((line = input.readLine()) != null && wpe.isAlive(line)) {
            		pipe.append(line);
            		pipe.append("\n");
            		//System.out.println(this.isAlive() +" "+ this.getState() +" "+ (input.ready()?"TRUE":"FALSE") +" "+ line.length() +" '"+ line +"'");
            	}
        	}
        	catch(IOException ioe){
        		ioe.printStackTrace();
        	}	    		
    	}
    }
}
