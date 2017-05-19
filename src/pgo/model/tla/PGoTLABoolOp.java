package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Statement;

/**
 * Represents a comparator or a binary boolean operation in TLA.
 *
 */
public class PGoTLABoolOp extends PGoTLA {

	private String token;

	private PGoTLA left;

	private PGoTLA right;

	public PGoTLABoolOp(String tok, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		this.token = tok;
		left = prev;
		right = next;
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
	
	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	public String toString() {
		return "PGoTLABoolOp (" + this.getLine() + "): (" + left.toString() + ") " + token
				+ " (" + right.toString() + ")";
	}
}
