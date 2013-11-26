package edu.ubc.webscarab;

/*  
 *  package explorer /src/edu.ubc.webscarab/
 *  folder directory /src/edu/ubc/webscarab/
 */

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.owasp.webscarab.httpclient.HTTPClient;
import org.owasp.webscarab.model.HttpUrl;
import org.owasp.webscarab.model.Request;
import org.owasp.webscarab.model.Response;
import org.owasp.webscarab.plugin.proxy.ProxyPlugin;

import edu.ubc.javascript.NodeUti1;

public class MyProxyPlugin extends ProxyPlugin {

	public static boolean PROFILE = false;
	private final Map<String, Transformer> transformers = new HashMap<String, Transformer>();
	
	public MyProxyPlugin() {
		super();
		transformers.put("InsertJScript", new InsertJScriptTransformer());
		transformers.put("Trace", new TraceTransformer());
	}
	
	@Override
	public String getPluginName() {
		return "MyProxyPlugin";
	}

	@Override
	public HTTPClient getProxyPlugin(HTTPClient in) {
		return new Plugin(in);
	}
    
	private class Plugin implements HTTPClient {

		private HTTPClient in;
		
		public Plugin(HTTPClient in) {
			this.in = in;
		}
		
		//@Override 
		public Response fetchResponse(Request request) throws IOException {
			HttpUrl url = request.getURL();			
			String href = "";
			if (url != null) {
				href = url.toString();
				NodeUti1.setURL(href);
				href = href.toLowerCase();				
			}
			
			long startFetch = System.currentTimeMillis();
			
			Response response = in.fetchResponse(request);
			long stopFetch = System.currentTimeMillis();
			if(PROFILE) {
				System.out.println("Fetch: " + (stopFetch - startFetch) + ": " + href);
			}
			
			if (href.contains("soundfont-ogg.js") || href.contains("data:audio") || href.contains("trazing")) {
			  return response;				
			}
			if (href.contains(".js") == true) {
				response.setHeader("Content-Type", "application/javascript");
			}
						
			if(response != null) {
				String cType = response.getHeader("Content-Type");
				if (cType != null) { 					
					cType = cType.toLowerCase();
					if (cType.contains("audio/")) {
						return response;
					}
					String charset = "UTF-8";//(cType.toLowerCase().contains("utf-8")) ? "UTF-8" : "ISO-8859-1";
					try {
						if (cType.contains("javascript") || cType.contains("text/x-js")) {
							if (href.contains("zzv2") || href.contains("firebug-lite") || href.contains("fbug.googlecode.com")) {
								return response;
							}							
							modifyResponse(href, response, charset, transformers.get("Trace"));
						} 
						else if (cType.contains("html")) {							
							if (href.contains("zzv2") && href.contains("openZZ")) {
							    return response;
							}
							modifyResponse(href, response, charset, transformers.get("InsertJScript"));
						}
					} 
					catch(Exception e) {
						throw new IOException(e);
					}
				}
			}			
			return response;
		}
		
		private void modifyResponse(String href, Response response, String charset, Transformer tx) throws IOException {
			long duration = System.currentTimeMillis();
			String data = new String(response.getContent(), charset);						
			String output = tx.transform(href, data);			
			response.setContent( output.getBytes(charset) );
			if (PROFILE) {
              System.out.println("Transfrom: "+ (System.currentTimeMillis()-duration));
			}
            return;			
		}
	}
}
