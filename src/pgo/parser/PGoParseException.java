package pgo.parser;

/**
 * An exception for pluscal parsing errors
 *
 */
public class PGoParseException extends Exception {

	private static final long serialVersionUID = 6371850492793748898L;

	public PGoParseException(String msg) {
		super(msg);
	}

	public PGoParseException(String msg, int lineN) {
		super(msg + " Line: " + lineN);
	}
}
