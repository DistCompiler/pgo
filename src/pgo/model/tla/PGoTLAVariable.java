package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoType;

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
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLAVar (" + this.getLine() + "): " + name;
	}
}
