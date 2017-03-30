package pgo;

/**
 * A PGo Exception consisting of a prefix (type of error) and a line number in
 * the pluscal file
 * 
 */
public abstract class PGoException extends Exception {

	private int line = -1;
	private String msg;
	private String prefix;

	public PGoException(String prefix, String msg) {
		super(prefix + " " + msg);
		msg = msg;
	}

	public PGoException(String prefix, String msg, int lineN) {
		super(prefix + " " + msg + " at Line: " + lineN);
		line = lineN;
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
