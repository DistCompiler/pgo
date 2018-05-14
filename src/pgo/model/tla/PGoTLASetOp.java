package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a binary set operation.
 */
public class PGoTLASetOp extends PGoTLAExpression {
	private String token;
	private PGoTLAExpression left, right;

	public PGoTLASetOp(String tok, PGoTLAExpression prev, PGoTLAExpression next, int line) {
		super(line);
		this.token = tok;
		this.left = prev;
		this.right = next;
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
		return "PGoTLASetOp (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString()
				+ ")";
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLASetOp) not implemented");
	}
}
