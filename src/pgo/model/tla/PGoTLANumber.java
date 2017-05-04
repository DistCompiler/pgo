package pgo.model.tla;

/**
 * Represents a tla token for a number
 *
 */
public class PGoTLANumber extends PGoTLA {

	private String val;

	public PGoTLANumber(String val, int line) {
		super(line);
		this.val = val;
	}

	public String getVal() {
		return val;
	}

	public String toString() {
		return "PGoTLANumber (" + this.getLine() + "): " + val;
	}
}
