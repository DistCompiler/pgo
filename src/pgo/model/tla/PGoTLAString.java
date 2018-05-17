package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;

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
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}
}
