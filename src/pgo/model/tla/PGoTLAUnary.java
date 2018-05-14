package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a TLA unary operator (negation, element union, or powerset) or a
 * predicate operation (CHOOSE, for all, exists)
 * 
 * ## Note:
 * 
 * With TLAParser, this will only ever be an actual TLA+ unary operator.
 * 
 */
public class PGoTLAUnary extends PGoTLAExpression {
	private String token;
	// The expression the operator operates on
	private PGoTLAExpression arg;

	public PGoTLAUnary(String tok, PGoTLAExpression arg, int line) {
		super(line);
		this.token = tok;
		this.arg = arg;
	}

	public String getToken() {
		return token;
	}

	public PGoTLAExpression getArg() {
		return arg;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	public String toString() {
		return "PGoTLAUnary (" + this.getLine() + "): " + token + " " + arg.toString();
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}
}
