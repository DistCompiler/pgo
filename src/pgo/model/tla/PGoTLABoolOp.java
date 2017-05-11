package pgo.model.tla;

/**
 * Represents a comparator or a binary boolean operation in TLA.
 *
 */
public class PGoTLABoolOp extends PGoTLA {

	private String token;

	private PGoTLA left;

	private PGoTLA right;

	public PGoTLABoolOp(String tok, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		switch (tok) {
		case "#":
		case "/=":
			this.token = "!=";
			break;
		case "/\\":
		case "\\land":
			this.token = "&&";
			break;
		case "\\/":
		case "\\lor":
			this.token = "||";
			break;
		case "=<":
		case "\\leq":
			this.token = "<=";
			break;
		case "\\geq":
			this.token = ">=";
			break;
		case "=":
			this.token = "==";
			break;
		default:
			this.token = tok;
			break;
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
		return "PGoTLABool (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString() + ")";
	}
}
