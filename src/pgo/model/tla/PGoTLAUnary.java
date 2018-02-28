package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a TLA unary operator (negation, element union, or powerset) or a
 * predicate operation (CHOOSE, for all, exists)
 * 
 */
public class PGoTLAUnary extends PGoTLA {
	private String token;
	// The expression the operator operates on
	private PGoTLA arg;

	public PGoTLAUnary(String tok, PGoTLA arg, int line) {
		super(line);
		this.token = tok;
		this.arg = arg;
	}

	public String getToken() {
		return token;
	}

	public PGoTLA getArg() {
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
}
