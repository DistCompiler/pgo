package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;
import pgo.model.golang.Token;

/**
 * Variable access in TLA Expr
 *
 */
public class PGoTLAVariable extends PGoTLA {

	private String name;

	public PGoTLAVariable(String n, int line) {
		super(line);
		name = n;
	}

	public String getName() {
		return name;
	}
	
	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();
		ret.add(new Token(String.valueOf(this.getName())));
		return ret;
	}
	
	public String toString() {
		return "PGoTLAVar (" + this.getLine() + "): " + name;
	}
}
