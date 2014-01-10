package ca.ubc.tklo.cvc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.HashSet;
import java.util.Set;

public class CVCsolverDOM {
	protected CVCemulatorWindows emulator;
	protected String cvc_dom; // assume it's ok to keep this in memory
	protected String cvc_slice;
	protected String output;
	protected Set<String> nodeIDs;
	protected Set<String> tempIDs;
	protected String sessionID;
	public CVCsolverDOM(CVCemulatorWindows emulator, String cvc_dom, String cvc_slice) {    	
    	this.emulator = emulator;
    	this.cvc_dom = cvc_dom;
    	this.cvc_slice = cvc_slice;
	}	
	protected String solve() {
		if (output == null) {
			StringBuffer input = new StringBuffer(cvc_dom);
			BufferedReader buf = new BufferedReader(new StringReader(cvc_slice));
			try {
				nodeIDs = new HashSet<String>();
				tempIDs = new HashSet<String>();
				String[] line = buf.readLine().split("[,\\s:]");
				sessionID = line[0];
				int sessionID_length = sessionID.length();				
				for (int i=1; i < line.length; ++i) {
					String token = line[i];
					if (token.length() > 0) {
						if (token.length() >= sessionID_length && token.substring(0, sessionID_length).equals(sessionID)) {
							tempIDs.add(token);
						}
						else {
							nodeIDs.add(token);
						}
					}
				}
			}
			catch (IOException e) {
				e.printStackTrace();
			}			
			input.append(cvc_slice);
			input.append("\rCHECKSAT;");
			input.append("\rWHERE;");		
			System.out.println("CVC input "+ input.length() +"<< "+ input);		
			output = emulator.process(input.toString());
	    	System.out.println("CVC output "+ output.length() +">> "+ output);
		}
		return output;		
	}
	protected Set<String> getNodeIDs() {
		return nodeIDs;
	}
	protected Set<String> getTempIDs() {
		return tempIDs;
	}
	protected String getSessionID() {
		return sessionID;
	}
	protected void quit() {
		this.emulator.quit();
	}
	protected boolean childIndexEQ(String nodeName, int index) {
		return (emulator.process("QUERY childIndex("+ nodeName +") ="+ index +";").equals("Valid.\n"));
	}
	protected boolean childIndexGT(String nodeName, int index) {
		return (emulator.process("QUERY childIndex("+ nodeName +") >"+ index +";").equals("Valid.\n"));
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
					strbuf.append("\r");
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
    public static void main(String[] args) {
    	String prefix = "Z:/git/ConcolicJS/smt/";
    	String cvcpath = prefix+ "cvc3-2.4.1-win32-optimized/bin/cvc3.exe +interactive"; 
    	String dompath = prefix+ "cvc3-DOM1.cvc";
    	String sespath = prefix+ "cvc3-example1.cvc";
    	CVCsolverDOM csd = new CVCsolverDOM(new CVCemulatorWindows(cvcpath), readWholeFile(dompath), readWholeFile(sespath));
    	String output = csd.solve();
    	csd.quit();
    	
    	// parse output of CVC, generate XML
    	String xmlpath = prefix+ "cvc3-exampleD.xml";
		XMLgenerator xmlg = new XMLgenerator(csd, new BufferedReader(new StringReader(output)) );
		XMLgenerator.outXML(xmlg.getDocument(), System.out);
		try {
			XMLgenerator.outXML(xmlg.getDocument(), new FileOutputStream(xmlpath));
		}
		catch (FileNotFoundException e) {
			e.printStackTrace();
		} 			
    }
}
