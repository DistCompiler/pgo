package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;

/**
 * Represents a tla token for a number
 *
 */
public class PGoTLANumber extends PGoTLAExpression {

	private String val;

	public PGoTLANumber(String val, int line) {
		super(line);
		this.val = val;
	}

	public String getVal() {
		return val;
	}
	
	protected Expression convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLANumber (" + this.getLine() + "): " + val;
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}
}
