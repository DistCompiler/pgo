package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;

/**
 * Represents a TLA unary operator: negation, element union, or powerset.
 * TODO predicate operations should probably also be handled by this class
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
	
	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();
		
		Vector<Statement> rightRes = this.getArg().toStatements();
		// the argument should be a single Expression
		assert (rightRes.size() == 1);
		assert (rightRes.get(0) instanceof Expression);
		
		switch (this.token) {
		case "~":
		case "\\lnot":
		case "\\neg":
			Vector<Expression> exp = new Vector<>();
			exp.add(new Token("!"));
			exp.add((Expression) rightRes.get(0));
			ret.add(new SimpleExpression(exp));
			break;
		case "UNION":
			// TODO (issue #18) implement
			break;
		case "SUBSET":
			FunctionCall fc = new FunctionCall("PowerSet", new Vector<>(), (Expression) rightRes.get(0));
			ret.add(fc);
			break;
		}
		return ret;
	}
	
	public String toString() {
		return "PGoTLAUnary (" + this.getLine() + "): " + token + " " + arg.toString();
	}
}
