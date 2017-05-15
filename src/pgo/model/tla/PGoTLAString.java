package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;
import pgo.model.golang.Token;

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
	
	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();
		ret.add(new Token(this.getString()));
		return ret;
	}
	
	public String toString() {
		return "PGoTLAString (" + this.getLine() + "): " + string;
	}
}
