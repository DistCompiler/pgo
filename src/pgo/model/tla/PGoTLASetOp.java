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
	
	/* 
	 * Helper method to map TLA set ops to Go mapset functions.
	 * This is necessary because Go does not have set operations.
	 * Note that \notin does not correspond directly to a mapset function.
	 * This is dealt with in PGoTransStageGoGen.tlaTokentoStatement().
	 * @return the Go mapset function name corresponding to the TLA set operation
	 */
	public String getGoFunc() {
		switch (token) {
		case "\\cup":
		case "\\union":
			return "Union";
		case "\\cap":
		case "\\intersect":
			return "Intersect";
		case "\\in":
			return "Contains";
		case "\\notin":
			return "NotIn";
		case "\\subseteq":
			return "IsSubset";
		case "\\":
			return "Difference";
		}
		assert(false);
		return null;
	}

	public String toString() {
		return "PGoTLASetOp (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString() + ")";
	}
}
