package pgo.model.tla;

/**
 * @author Brandon Zhang
 * Represents a binary set operation.
 */
public class PGoTLASetOp extends PGoTLA {
	private String token;
	private PGoTLA left, right;

	public PGoTLASetOp(String tok, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		this.token = tok;
		this.left = prev;
		this.right = next;
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
		return "PGoTLASetOp (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString() + ")";
	}
}
