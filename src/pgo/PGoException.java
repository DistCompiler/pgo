package pgo;

/**
 * A PGo Exception consisting of a prefix (type of error) and a line number in
 * the pluscal file
 *
 */
public abstract class PGoException extends RuntimeException {
	private final int line;
	private final String msg;
	private final String prefix;

	public PGoException(String prefix, String msg) {
		super(prefix + ": " + msg);
		this.prefix = prefix;
		this.msg = msg;
		this.line = -1;
	}

	public PGoException(String prefix, String msg, int lineN) {
		super(prefix + ": " + msg + " at Line: " + lineN);
		this.prefix = prefix;
		this.line = lineN;
		this.msg = msg;
	}

	public String getMsg() {
		return msg;
	}

	public String getPrefix() {
		return prefix;
	}

	public int getLine() {
		return line;
	}
}
