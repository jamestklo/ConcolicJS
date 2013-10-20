package ca.ubc.tklo.cvc;

import java.util.ArrayList;
import java.util.List;

import com.google.common.base.Joiner;

import ca.ubc.salt.concolicjs.WindowsProcessEmulator;

public class CVCemulatorWindows extends WindowsProcessEmulator {

	public CVCemulatorWindows(String command) {
		super(command);
	}

	@Override
	protected boolean isAlive(String line) {
		return (! line.equals("Valid."));
	}
    /**
     * @param args
     */
    public static void main(String[] args) {
    	
    	String prefix = "C:/Temp";    	
    	WindowsProcessEmulator tcc = new CVCemulatorWindows(prefix+ "/cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive");
    	int counter = 0;    	
    	String str;
    	List<String> input;

    	input = new ArrayList<String>();
    	input.add("a, b:INT;");
    	input.add("ASSERT a > b AND b > 0;");
    	input.add("CHECKSAT;");
    	input.add("WHERE;");
    	input.add("QUERY TRUE;");
    	str = Joiner.on("\r").join(input);
    	System.out.println(counter++ +" "+ str);
    	System.out.println(tcc.process(str));
    	
    	input = new ArrayList<String>();
    	input.add("QUERY a > 0;");
    	input.add("QUERY TRUE;");
    	str = Joiner.on("\r").join(input); 
    	System.out.println(counter++ +" "+ str);
    	System.out.println(tcc.process(str));
    	
    	input = new ArrayList<String>();
    	input.add("c, d:INT;");
    	input.add("ASSERT c > d AND d > 0;");
    	input.add("CHECKSAT;");
    	input.add("WHERE;");
    	input.add("QUERY TRUE;");
    	str = Joiner.on("\r").join(input);
    	System.out.println(counter++ +" "+ str);
    	System.out.println(tcc.process(str));
    }	
}
