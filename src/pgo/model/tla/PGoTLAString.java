package pgo.model.tla;

/**
 * Represents a TLA token string
 * 
 *
 */
public class PGoTLAString extends PGoTLA {

	private String string;

	public PGoTLAString(String string, int line) {
		super(line);
		this.string = string;
	}

	public String getString() {
		return string;
	}
	
	public String toString() {
		return "PGoTLAString (" + this.getLine() + "): " + string;
	}
}
