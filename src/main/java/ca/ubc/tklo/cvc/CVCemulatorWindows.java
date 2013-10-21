package ca.ubc.tklo.cvc;

import java.util.ArrayList;
import java.util.List;

import com.google.common.base.Joiner;

public class CVCemulatorWindows extends WindowsProcessEmulator {

	public CVCemulatorWindows(String cvcpath) {
		super(cvcpath);
	}
	public CVCemulatorWindows(List<String> cvccmds) {
		super(cvccmds);
	}

	@Override
	public String process(String str) {
		return super.process(str+"\rQUERY TRUE;").substring(5);
	}
	
	@Override
	protected boolean isAlive(String input, String line) {
		return (! line.equals("Valid."));
	}	
	
    /**
     * @param args
     */
    public static void main(String[] args) {
    	String prefix = "C:/Temp/tklo/cvc4"; 
    	CVCemulatorWindows tcc = new CVCemulatorWindows(prefix+ "/cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive");
    	int counter = 0;    	
    	String str;
    	List<String> input;

    	input = new ArrayList<String>();
    	input.add("a, b:INT;");
    	input.add("ASSERT a > b AND b > 0;");
    	input.add("CHECKSAT;");
    	input.add("WHERE;");
    	str = Joiner.on("\r").join(input);
    	System.out.println(counter +" << "+ str);
    	System.out.println(counter +" >> "+ tcc.process(str));
    	++counter;
    	
    	input = new ArrayList<String>();
    	input.add("QUERY a > 0;");
    	str = Joiner.on("\r").join(input); 
    	System.out.println(counter +" << "+ str);
    	System.out.println(counter +" >> "+ tcc.process(str));
    	++counter;
    	
    	input = new ArrayList<String>();
    	input.add("c, d:INT;");
    	input.add("ASSERT c > d AND d > 0;");
    	input.add("CHECKSAT;");
    	input.add("WHERE;");
    	str = Joiner.on("\r").join(input);
    	System.out.println(counter +" << "+ str);
    	System.out.println(counter +" >> "+ tcc.process(str));
    	++counter;

    	tcc.quit();
    }
}
