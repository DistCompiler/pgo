package pgo.parser;

import pgo.PGoException;

/**
 * An exception for pluscal parsing errors
 *
 */
public class PGoParseException extends PGoException {

	private static final long serialVersionUID = 6371850492793748898L;
	private static final String prefix = "Parse Error";

	public PGoParseException(String msg) {
		super(prefix, msg);
	}

	public PGoParseException(String msg, int lineN) {
		super(prefix, msg, lineN);
	}
}
