package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		result = prime * result + ((token == null) ? 0 : token.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLASimpleArithmetic other = (PGoTLASimpleArithmetic) obj;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (right == null) {
			if (other.right != null)
				return false;
		} else if (!right.equals(other.right))
			return false;
		if (token == null) {
			if (other.token != null)
				return false;
		} else if (!token.equals(other.token))
			return false;
		return true;
	}
}
