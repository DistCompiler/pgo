package pgo.formatters;

import java.io.IOException;
import java.io.Writer;

public class IndentingWriter extends Writer {
	
	Writer out;
	int indent = 0;
	String tab;
	boolean shouldIndent = false;
	
	public IndentingWriter(Writer out) {
		this.out = out;
		this.tab = "    ";
	}
	
	public IndentingWriter(Writer out, String tab) {
		this.out = out;
		this.tab = tab;
	}

	@Override
	public void close() throws IOException {
		out.close();
	}

	@Override
	public void flush() throws IOException {
		out.flush();
	}

	@Override
	public void write(char[] chars, int offset, int len) throws IOException {
		String lf = System.lineSeparator();
		String data = String.valueOf(chars, offset, len);
		int start = 0;
		while(true) {
			if(shouldIndent) {
				for(int i = 0; i < indent; ++i) {
					out.write(tab);
				}
				shouldIndent = false;
			}
			int next = data.indexOf(lf, start);
			if(next != -1) {
				out.write(data.substring(start, next+lf.length()));
				start = next + lf.length();
				shouldIndent = true;
				if(start == data.length()) {
					break;
				}
			}else {
				out.write(data.substring(start));
				break;
			}
		}
	}

}
