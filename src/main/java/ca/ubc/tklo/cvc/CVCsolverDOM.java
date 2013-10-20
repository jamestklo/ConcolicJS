package ca.ubc.tklo.cvc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.Iterator;

public class CVCsolverDOM {
	protected CVCemulatorWindows emulator;
	String cvc_dom; // assume it's ok to keep this in memory
	String cvc_slice;
	public CVCsolverDOM(CVCemulatorWindows emulator, String cvc_dom, String cvc_slice) {    	
    	this.emulator = emulator;
    	this.cvc_dom = cvc_dom;
    	this.cvc_slice = cvc_slice;
	}
	protected String solve() {
		return emulator.process(cvc_dom + cvc_slice);
	}
	protected static String readWholeFile(String filepath) {
		File file = new File(filepath);
		if (file.canRead()) {
			try {
				StringBuffer strbuf = new StringBuffer();
				BufferedReader reader = new BufferedReader(new FileReader(file));
				String line;
				while ((line = reader.readLine()) != null) {
					strbuf.append(line);
				}
				reader.close();
				return strbuf.toString();
			} 
			catch (IOException e) {
				e.printStackTrace();
			}
		}		
		return null;
	}
	protected boolean childIndexEQ(String nodeName, int index) {
		return (emulator.process("QUERY childIndex("+ nodeName +") ="+ index +";").equals("Valid.\n"));
	}
	protected boolean childIndexGT(String nodeName, int index) {
		return (emulator.process("QUERY childIndex("+ nodeName +") >"+ index +";").equals("Valid.\n"));
	}
    public static void main(String[] args) {
    	String prefix = "C:/Temp";    	
    	//String prefix = "Z:/cvc4";
    	String cvcpath = prefix+ "/cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive";
    	String dompath = "cvc3-DOMemulation1.cvc";
    	String sespath = prefix+ "cvc3-example1.cvc";
    	CVCsolverDOM csd = new CVCsolverDOM(new CVCemulatorWindows(cvcpath), readWholeFile(dompath), readWholeFile(sespath));
    	String output = csd.solve();

    	// parse output of CVC, generate XML
		XMLgenerator xmlg = new XMLgenerator(csd, new BufferedReader(new StringReader(output)) );
		XMLgenerator.outXML(xmlg.toDOM(null), System.out);
		System.out.println("\n");
    	
		Iterator<CVCnode> itr_cvc = xmlg.getNodeSet().iterator();
		while (itr_cvc.hasNext()) {
			System.out.println(itr_cvc.next().getAliases().toString());
		}
    }
}
