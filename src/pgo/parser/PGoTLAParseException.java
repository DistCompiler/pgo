package pgo.parser;

import pgo.PGoException;

public class PGoTLAParseException extends PGoException {
	private static final long serialVersionUID = -2848974254941388892L;
	String got;
	String[] options;

	public PGoTLAParseException(int line, String got, String[] options) {
		super("TLA Parse Error", "Got "+got+" when expecting one of "+String.join(", ", options), line);
		this.got = got;
		this.options = options;
	}
	
	public PGoTLAParseException(int line, String got) {
		super("TLA Parse Error", "Unexpected "+got, line);
	}

}
