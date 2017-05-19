package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

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

	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLABool (" + this.getLine() + "): " + val;
	}
}
