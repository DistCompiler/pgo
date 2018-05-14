package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a simple arithmetic operation written in TLA
 * Don't need to care about order of operation, as the output go code, as long as
 * written equivalent to TLA+, will do order of operation
 *
 */
public class PGoTLASimpleArithmetic extends PGoTLAExpression {

	// the arithmetic token
	private String token;

	// the left side
	private PGoTLAExpression left;

	// the right side
	private PGoTLAExpression right;

	public PGoTLASimpleArithmetic(String t, PGoTLAExpression prev, PGoTLAExpression next, int line) {
		super(line);
		token = t;
		left = prev;
		right = next;
	}

	public String getToken() {
		return token;
	}

	public PGoTLAExpression getLeft() {
		return left;
	}

	public PGoTLAExpression getRight() {
		return right;
	}
	
	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLASimpArith (" + this.getLine() + "): (" + left.toString() + ") " + token
				+ " (" + right.toString() + ")";
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLASimpleArithmetic) not implemented");
	}
}
