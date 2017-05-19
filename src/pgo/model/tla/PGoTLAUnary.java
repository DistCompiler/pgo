package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

/**
 * Represents a TLA unary operator: negation, element union, or powerset. TODO
 * predicate operations should probably also be handled by this class
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
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLAUnary (" + this.getLine() + "): " + token + " " + arg.toString();
	}
}
