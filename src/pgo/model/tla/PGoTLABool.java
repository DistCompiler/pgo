package pgo.model.tla;

public class PGoTLABool extends PGoTLA {

	private boolean val;

	public PGoTLABool(String b, int line) {
		super(line);
		if (b.equals("TRUE")) {
			val = true;
		} else if (b.equals("FALSE")) {
			val = false;
		} else {
			assert (false);
		}
	}

	public boolean getVal() {
		return val;
	}
	
	public String toString() {
		return "PGoTLABool (" + this.getLine() + "): " + val;
	}
}
