package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;

public class PGoTLABool extends PGoTLAExpression {

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

	protected Expression convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLABool (" + this.getLine() + "): " + val;
	}
}
