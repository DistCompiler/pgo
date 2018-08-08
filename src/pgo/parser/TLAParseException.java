package pgo.parser;

import pgo.formatters.IndentingWriter;
import pgo.util.SourceLocation;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Set;

@SuppressWarnings("serial")
public class TLAParseException extends Exception {
	private NavigableMap<SourceLocation, Set<ParseFailure>> reason;

	private static String getReasonString(NavigableMap<SourceLocation, Set<ParseFailure>> map) {
		Map.Entry<SourceLocation, Set<ParseFailure>> e = map.lastEntry();
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try {
			out.write("Parse failure at "+e.getKey()+":");
			try(IndentingWriter.Indent i_ = out.indent()){
				for(ParseFailure f : e.getValue()) {
					out.newLine();
					out.write(f.toString());
				}
			}
		} catch (IOException e1) {
			throw new RuntimeException("string writers should not throw IO errors", e1);
		}
		return w.toString();
	}

	public TLAParseException(NavigableMap<SourceLocation, Set<ParseFailure>> reason) {
		super(getReasonString(reason));
		this.reason = reason;
	}
	
	public NavigableMap<SourceLocation, Set<ParseFailure>> getReason() {
		return reason;
	}

}
