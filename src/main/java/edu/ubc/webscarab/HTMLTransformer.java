package edu.ubc.webscarab;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.StringReader;
import java.io.Reader;

import edu.ubc.javascript.NodeUti1;

public class HTMLTransformer {
	private Reader input;
	private StringBuffer output;
	private boolean inScript = false;
	private StringBuffer buffer = new StringBuffer();
	private Transformer transformer;
	private int scriptCount = 0;
	
	public HTMLTransformer(Reader input, StringBuffer output, Transformer rtb) throws FileNotFoundException {
		this.input = input;
		this.output = output;
		this.transformer = rtb;
	}
	
	private void finishScript() throws Exception {
		inScript = false;
		buffer.delete(buffer.length()-9, buffer.length());
		try {
			String script = buffer.toString();
			if (script.length() > 0) {
				NodeUti1.scriptCount.set(++scriptCount);
				script = this.transformer.transform(new StringReader(script));
			}					
			output.append(script + "</script>");
			buffer = new StringBuffer();
		} 
		catch(Exception e) {
			System.err.println(buffer);
			System.err.println("------------------------------------------");
			output.append(buffer + "</script>");
			buffer = new StringBuffer();
		}
	}
	
	private int read() throws IOException {
		int retVal = input.read();
		if(inScript) {
			buffer.append((char) retVal);
		} else {
			output.append((char) retVal);
		}
		return retVal;
	}

	public void readTagClose() throws Exception {
		int a = read();
		while(a != -1) {
			if(a == '>') {
				return;
			} 
			a = read();
		}
	}
	
	public void readTagOpen() throws Exception {
		int a = read();
		while(a != -1) {
			if(a == '/') {
				a = read();
				if(a == '>') {
					return;
				} 
			} 
			if(a == '>') {
				return;
			} 
			a = read();
		}
	}
	
	public void readScriptTag() throws Exception {
		int c = read();
		if((c=='c')) {
			int r = read();
			if((r=='r')) {
				int i = read();
				if((i=='i')) {
					int p = read();
					if((p=='p')) {
						int t = read();
						if(t=='t') {
							readTagOpen();
							inScript = true;
							readScriptBody();
							finishScript();
						} 
					} 
				} 
			} 
		} 
	}
	
	public void readScriptBody() throws Exception {
		int a = read();
		while(a != -1) {
			if(a=='<') {
				int slash = read();
				if((slash == '/')) {
					int s = read();
					if((s == 's')) {
						int c = read();
						if((c=='c')) {
							int r = read();
							
							if((r=='r')) {
								int i = read();
								
								if((i=='i')) {
									int p = read();
									
									if((p=='p')) {
										int t = read();
										
										if(t=='t') {
											int gt = read();
											
											if(gt=='>') {
												
												return;
											}
										}
									}
								}
							}
						}
					}
				}
			} 
			a = read();
		}
	}
	
	public void readDocTypeBody() throws Exception {
		int a = read();
		while(a != -1) {
			if(a == '>') {
				return;
			}
			a = read();
		}
	}
	
	public void readCommentBody() throws Exception {
		int a = read();
		while(a != -1) {
			if(a == '-') {
				a = read();
				if(a == '-') {
					a = read();
					if(a == '>') {
						return;
					}
				}
			} 
			a = read();
		}
	}
	
	public void readComment() throws Exception {
		int a = read();
		if(a == '-') {
			 a = read();
			 if(a == '-') {
				 readCommentBody();
			 } else {
				 throw new RuntimeException("Malformed XML comment:");
			 }
		} else {
			 readDocTypeBody();
		}
		
	}
	
	public void readLT() throws Exception {
		int a = read();
		if(a == 's') {
			readScriptTag();
		} else if(a == '/'){
			readTagClose();
		} else if(a == '!') {
			readComment();
		} else {
			readTagOpen();
		}
	}
	
	public void run() throws Exception {
		int a = read();
		while(a != -1) {
			if(a == '<') {
				readLT();
			} 
			if(!input.ready()) {
				return;
			}
			a = read();
		}
		NodeUti1.scriptCount.set(0);
	}

}

