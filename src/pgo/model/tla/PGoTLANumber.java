package pgo.model.tla;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pgo.model.golang.Statement;
import pgo.model.golang.Token;

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

	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();
		ret.add(new Token(this.getVal()));
		return ret;
	}
	
	protected Set<String> getImports() {
		return new HashSet<>();
	}

	public String toString() {
		return "PGoTLANumber (" + this.getLine() + "): " + val;
	}
}
