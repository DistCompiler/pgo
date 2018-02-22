package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a comparator or a binary boolean operation in TLA.
 *
 */
public class PGoTLABoolOp extends PGoTLAExpression {

	private String token;

	private PGoTLAExpression left;

	private PGoTLAExpression right;

	public PGoTLABoolOp(String tok, PGoTLAExpression prev, PGoTLAExpression next, int line) {
		super(line);
		this.token = tok;
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
		return "PGoTLABoolOp (" + this.getLine() + "): (" + left.toString() + ") " + token
				+ " (" + right.toString() + ")";
	}
}
