package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;

/**
 * Represents a TLA token string
 * 
 */
public class PGoTLAString extends PGoTLAExpression {

	private String string;

	public PGoTLAString(String string, int line) {
		super(line);
		this.string = string;
	}

	public String getString() {
		return string;
	}
	
	protected Expression convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLAString (" + this.getLine() + "): " + string;
	}
}
