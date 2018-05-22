package pgo.formatters;

import java.io.IOException;
import java.io.Writer;

public class IndentingWriter extends Writer {
	
	Writer out;
	int indent = 0;
	boolean shouldIndent = false;
	int defaultIndent = 4;
	int horizontalPosition = 0;
	
	public static class Indent implements AutoCloseable {
		
		IndentingWriter writer;
		int spaces;

		public Indent(IndentingWriter writer, int spaces) {
			this.writer = writer;
			this.spaces = spaces;
		}

		@Override
		public void close() {
			writer.unindent(spaces);
		}

	}
	
	public Indent indent(int spaces) {
		indent += spaces;
		return new Indent(this, spaces);
	}
	
	public Indent indent() {
		return indent(defaultIndent);
	}
	
	public Indent indentToPosition() {
		return indentToPosition(horizontalPosition);
	}
	
	/**
	 * @return the 0-based position along the current line of text being written
	 */
	public int getHorizontalPosition() {
		return horizontalPosition;
	}
	
	/**
	 * 
	 * Indents any following lines such that they start at position
	 * 
	 * @param position 
	 * @return an AutoCloseable the will reverse the indent when closed
	 */
	public Indent indentToPosition(int position) {
		return indent(position - indent);
	}
	
	public void unindent(int spaces) {
		if(spaces > indent) {
			throw new RuntimeException("can't unindent below 0");
		}
		indent -= spaces;
	}
	
	public IndentingWriter(Writer out) {
		this.out = out;
	}
	
	public IndentingWriter(Writer out, int defaultIndent) {
		this.out = out;
		this.defaultIndent = defaultIndent;
	}

	@Override
	public void close() throws IOException {
		out.close();
	}

	@Override
	public void flush() throws IOException {
		out.flush();
	}
	
	public void newLine() throws IOException {
		write(System.lineSeparator());
	}

	@Override
	public void write(char[] chars, int offset, int len) throws IOException {
		String lf = System.lineSeparator();
		String data = String.valueOf(chars, offset, len);
		int start = 0;
		while(true) {
			if(shouldIndent) {
				for(int i = 0; i < indent; ++i) {
					out.write(" ");
				}
				shouldIndent = false;
				horizontalPosition = 0;
			}
			int next = data.indexOf(lf, start);
			if(next != -1) {
				horizontalPosition += next + lf.length() - start;
				out.write(data.substring(start, next+lf.length()));
				start = next + lf.length();
				shouldIndent = true;
				if(start == data.length()) {
					break;
				}
			}else {
				horizontalPosition += data.length() - start;
				out.write(data.substring(start));
				break;
			}
		}
	}

}
