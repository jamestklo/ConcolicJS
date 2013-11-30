package edu.ubc.webscarab;

import java.io.IOException;
import java.util.ArrayList;

// ec2-23-20-34-25.compute-1.amazonaws.com
public class InsertJScriptTransformer implements Transformer {
	
	// private static String host = "http://184.73.167.93/zzv2/client-js/";	 
	private static String host = "http://www.ugrad.cs.ubc.ca/~k5r4/nbpAFZyrx5o/";
	// 6c03c3724338e041428613752dd5d40a		

	// insert our own scripts
	protected static String insertedJs = generateInsertedJs(host);
	
	protected static Transformer tf = new TraceTransformer(); // new ClosureTransformer();	
	
	//@Override // r is response-body
	public String transform(String href, String html) throws IOException {
		if ((href.indexOf("genoverse") >= 0 && html.contains("// Specify container element with css/jquery selector style")) 
		 || html.contains("QWERTY")) {			
		}
		else {
			Transformer tx = new AttrTransformer(tf);
			html = tx.transform(href, html);
		}
		
		html = html.replaceAll("<html manifest=\"offline.appcache\">", "<html>");
		html = html.replaceAll("http://72182.hittail.com/mlt.js", "http://www.ugrad.cs.ubc.ca/~k5r4/domtris/mlt.js");
		html = html.replaceAll("https://", "http://").replaceAll("jquery.min.js", "jquery.js").replaceAll("jquery-1.6.2.min.js", "jquery-1.6.2.js");
		
		String lowerCase = html.toLowerCase();

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
			index0 = html.toLowerCase().indexOf("</html>");		  
		}

		if (index0 >= 0) {
			index0 += pattern.length();
			String front = html.substring(0, index0);
			String ending = html.substring(index0);			
			String fnCounter = "";//"<script type='text/javascript'>if(! __xhr) { try {var __xhr = new XMLHttpRequest(); __xhr.open('GET', window.location.origin+'/notarealwebsiteurl', false); __xhr.send();} catch(e) {} }</script>";			
			html = front +"\n"+ fnCounter +"\n"+ insertedJs +"\n"+ ending;
		}
		
		// temporary removes the mysterious ? that appears at the end of page
		// needs more in-depth investigation into HTMLTransformer.java
		while ( html.length() > 0 && ((int) html.charAt(html.length()-1)) == 65535) {
			html = html.substring(0, html.length()-1);		  
		}
		return html;		
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
	  
	  srcs.add(host+"tracing/trazing/logString.js");
	  srcs.add(host+"tracing/trazing/logEval.js");
	  
	  srcs.add(host+"tracing/trazing/tagNative.js");		  	 
	  return srcs.toArray(new String[srcs.size()]);
	}
}
