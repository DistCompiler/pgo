package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a binary set operation.
 */
public class PGoTLASetOp extends PGoTLA {
	private String token;
	private PGoTLA left, right;

	public PGoTLASetOp(String tok, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		this.token = tok;
		this.left = prev;
		this.right = next;
	}

	public String getToken() {
		return token;
	}

	public PGoTLA getLeft() {
		return left;
	}

	public PGoTLA getRight() {
		return right;
	}
	
	protected Vector<Statement> convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLASetOp (" + this.getLine() + "): (" + left.toString() + ") " + token + " (" + right.toString()
				+ ")";
	}
}
