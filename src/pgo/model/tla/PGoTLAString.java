package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

/**
 * Represents a TLA token string
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
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLAString (" + this.getLine() + "): " + string;
	}
}
