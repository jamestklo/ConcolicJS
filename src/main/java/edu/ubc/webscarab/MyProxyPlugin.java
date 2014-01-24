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
	private static final String charset = "UTF-8";//(cType.toLowerCase().contains("utf-8")) ? "UTF-8" : "ISO-8859-1";
	
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
		return new Plugin(in, transformers);
	}
    
	private static class Plugin implements HTTPClient {
		private HTTPClient in;
		private final Map<String, Transformer> transformers;
		public Plugin(HTTPClient in, Map<String, Transformer> transformers) {
			this.in = in;
			this.transformers = transformers;
		}
		
		//@Override 
		/* (non-Javadoc)
		 * @see org.owasp.webscarab.httpclient.HTTPClient#fetchResponse(org.owasp.webscarab.model.Request)
		 */
		/* (non-Javadoc)
		 * @see org.owasp.webscarab.httpclient.HTTPClient#fetchResponse(org.owasp.webscarab.model.Request)
		 */
		/* (non-Javadoc)
		 * @see org.owasp.webscarab.httpclient.HTTPClient#fetchResponse(org.owasp.webscarab.model.Request)
		 */
		/* (non-Javadoc)
		 * @see org.owasp.webscarab.httpclient.HTTPClient#fetchResponse(org.owasp.webscarab.model.Request)
		 */
		public Response fetchResponse(Request request) throws IOException {
			HttpUrl url = request.getURL();			
			String href = "";
			if (url != null) {
				href = url.toString();
				NodeUti1.setURL(href);
				href = href.toLowerCase();				
			}
			Response response = null;
			
			String txmode = request.getHeader("Content-Type");
			if (txmode != null && txmode.equals("application/__txcode")) {				
				response = new Response();
				response.setContent(request.getContent());
				modifyResponse(href, response, "UTF-8", transformers.get("Trace"));
				return response;
			}
			
			long startFetch = System.currentTimeMillis();			
			response = in.fetchResponse(request);
			long stopFetch = System.currentTimeMillis();
			if(PROFILE) {
				System.out.println("Fetch: " + (stopFetch - startFetch) + ": " + href);
			}
			
			if (href.contains("soundfont-ogg.js") || href.contains("data:audio") || href.contains("trazing")) {
			  return response;				
			}
			if (href.endsWith(".js")) {
				response.setHeader("Content-Type", "application/javascript");
			}
			else if (href.endsWith(".html") || href.endsWith(".htm")) {
				response.setHeader("Content-Type", "text/html");
			}
						
			if(response != null) {
				String cType = response.getHeader("Content-Type");
				if (cType != null) { 					
					cType = cType.toLowerCase();
					if (cType.contains("audio/")) {
						return response;
					}
					try {
						if (cType.contains("javascript") || cType.contains("text/x-js")) {
							if (href.contains("zzv2") 
							 || href.contains("http://code.jquery.com:80/qunit/qunit-")
							 || href.endsWith("-qunit.js")
							 || href.contains("firebug-lite") 
							 || href.contains("fbug.googlecode.com")) {
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
		
		private Response modifyResponse(String href, Response response, String charset, Transformer tx) throws IOException {
			long duration = System.currentTimeMillis();
			String data = new String(response.getContent(), charset);						
			String output = tx.transform(href, data);
			response.setContent( output.getBytes(charset) );
			if (PROFILE) {
              System.out.println("Transfrom: "+ (System.currentTimeMillis()-duration));
			}
            return response;			
		}
	}
}
