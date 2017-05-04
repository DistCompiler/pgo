package pgo.model.tla;

/**
 * Represents a simple arithmetic operation written in TLA Don't need to care
 * about order of operation, as the output go code, as long as written
 * equivalent to TLA+, will do order of operation
 *
 */
public class PGoTLASimpleArithmetic extends PGoTLA {

	// the arithmetic token
	private String token;

	// the left side
	private PGoTLA left;

	// the right side
	private PGoTLA right;

	public PGoTLASimpleArithmetic(String t, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		token = t;
		if (token.equals("^")) {
			// replace exponent
			token = "**";
		}
		left = prev;
		right = next;
	}

	public String getToken() {
		return token;
	}

	public PGoTLA getLeft() {
		return left;
	}

	public PGoTLA getRight() {
		return right;
	}
	
	public String toString() {
		return "PGoTLASimpArith (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString() + ")";
	}
}
