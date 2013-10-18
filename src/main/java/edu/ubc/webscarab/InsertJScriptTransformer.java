package edu.ubc.webscarab;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;

import com.google.javascript.jscomp.NodeTraversal.Callback;

// ec2-23-20-34-25.compute-1.amazonaws.com
public class InsertJScriptTransformer implements Transformer {
	
	// private static String host = "http://184.73.167.93/zzv2/client-js/";	 
	private static String host = "http://www.ugrad.cs.ubc.ca/~k5r4/nbpAFZyrx5o/";
	// 6c03c3724338e041428613752dd5d40a		

	// insert our own scripts
	protected static String insertedJs = generateInsertedJs(host);
	public static ThreadLocal<Boolean> skip = new ThreadLocal<Boolean>() {
		public Boolean initialValue() {
			return false;
		}
	};
	
	protected static Transformer tf = new TraceTransformer(); // new ClosureTransformer();	
	
	//@Override // r is response-body
	public String transform(Reader r) throws IOException {		
		// read the html file
		char[] buffer = new char[262144]; 
		int n = r.read(buffer);
		StringBuffer buf = new StringBuffer();
		while(n != -1) {
		  buf.append(buffer, 0, n);
		  n = r.read(buffer);
		}
		
		// allHTML is html_source of the webpage
		// parse & modify html file, insert scripts after <head>, 
		// may have to append-after <body> as back-up
		String allHTML = buf.toString();					
		//allHTML = allHTML.replaceAll("<html manifest=\"offline.appcache\">", "<html>");
		//allHTML = allHTML.replaceAll("http://72182.hittail.com/mlt.js", "http://www.ugrad.cs.ubc.ca/~k5r4/domtris/mlt.js");
		allHTML = allHTML.replaceAll("https://", "http://").replaceAll("jquery.min.js", "jquery.js");
		
		String lowerCase = allHTML.toLowerCase();

		// at first, try appending scripts just before </head>
		String pattern = "<head>";		
		int index0 = lowerCase.indexOf(pattern);

		// try appending after <head> first, then <body> if <head> does not work
		// a webpage that has frames has no body		
		if (index0 < 0) {
			pattern = "<body>";
			index0 = lowerCase.indexOf(pattern);		
		} 

		// web_page has neither <head> or <body>
		if (index0 < 0) {
		  index0 = allHTML.toLowerCase().indexOf("</html>");		  
		}

		if (index0 >= 0) {
			index0 += pattern.length();
			String front = allHTML.substring(0, index0);
			String ending = allHTML.substring(index0);			
			String fnCounter = "";//"<script type='text/javascript'>if(! __xhr) { try {var __xhr = new XMLHttpRequest(); __xhr.open('GET', window.location.origin+'/notarealwebsiteurl', false); __xhr.send();} catch(e) {} }</script>";			
			allHTML = front +"\n"+ fnCounter +"\n"+ insertedJs +"\n"+ ending;
		}
		
		//return allHTML;
		String outputstr = null;
		if (skip.get() || allHTML.contains("QWERTY")) {
			outputstr = allHTML;
		}
		else {
			StringBuffer output = new StringBuffer();			
			HTMLTransformer tx = new HTMLTransformer(new StringReader(allHTML), output, tf);
			try {
				tx.run();
			} 
			catch (Exception e) {
				throw new RuntimeException(e);
			}		  
			outputstr = output.toString();
		}

		// temporary removes the mysterious ? that appears at the end of page
		// needs more in-depth investigation into HTMLTransformer.java
		while ( outputstr.length() > 0 && ((int) outputstr.charAt(outputstr.length()-1)) == 65535) {
		  outputstr = outputstr.substring(0, outputstr.length()-1);		  
		}
		return outputstr;		
	}

	private static String generateInsertedJs(String host) {		
		String sources[] = getSources(host);		
		int i=0, l=sources.length;
		StringBuffer inserts = new StringBuffer();
		for (i=0; i < l; i++) {
			inserts.append(getScriptHTML(sources[i])); 	
		}
		return inserts.toString();
	}
	
	private static String getScriptHTML(String source) {
	  StringBuffer script = new StringBuffer("<script type='text/javascript' src='");
	  script.append(source);
	  script.append("'></script>\n");
	  return script.toString();
	}
	
	private static String[] getSources(String host) {		
	  // Future: read srcs from a file, hard-coding for now
	  ArrayList<String> srcs = new ArrayList<String>();	  

	  // logging
	  //srcs.add(host+"tracing/trazing/instrument.js");
	  srcs.add(host+"tracing/trazing/logCall.js");
	  srcs.add(host+"tracing/trazing/anaCall.js");
	  //srcs.add(host+"tracing/trazing/xmlCall.js");
	  srcs.add(host+"tracing/trazing/cvcCall.js");
	  
	  srcs.add(host+"tracing/trazing/logAST.js");
	  srcs.add(host+"tracing/trazing/logCond.js");
	  //srcs.add(host+"tracing/trazing/logDOM.js");
	  srcs.add(host+"tracing/trazing/logFunc.js");
	  
	  srcs.add(host+"tracing/trazing/tagNative.js");		  	 
	  return srcs.toArray(new String[srcs.size()]);
	}
}
