package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;

/**
 * Variable access in TLA Expr
 *
 */
public class PGoTLAVariable extends PGoTLAExpression {

	private String name;

	public PGoTLAVariable(String n, int line) {
		super(line);
		name = n;
	}

	public String getName() {
		return name;
	}
	
	protected Expression convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLAVar (" + this.getLine() + "): " + name;
	}
}
