package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

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
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLAVar (" + this.getLine() + "): " + name;
	}
}
