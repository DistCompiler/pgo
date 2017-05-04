package pgo.model.tla;

/**
 * Represents a comparator in TLA.
 *
 */
public class PGoTLAComparator extends PGoTLA {

	private String token;

	private PGoTLA left;

	private PGoTLA right;

	public PGoTLAComparator(String comp, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		if (comp.equals("#") || comp.equals("/=")) {
			token = "!=";
		} else {
			token = comp;
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
		return "PGoTLAComp (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString() + ")";
	}
}
