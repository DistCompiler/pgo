package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;

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

	protected Vector<Statement> toStatements() {
		// TODO (issue #22) we need to see whether we are operating on sets
		Vector<Statement> ret = new Vector<>();

		Vector<Statement> leftRes = this.getLeft().toStatements();
		Vector<Statement> rightRes = this.getRight().toStatements();

		// comparators operations should just be a single SimpleExpression
		assert (leftRes.size() == 1);
		assert (rightRes.size() == 1);
		assert (leftRes.get(0) instanceof Expression);
		assert (rightRes.get(0) instanceof Expression);

		String tok = this.getToken();
		switch (tok) {
		case "#":
		case "/=":
			tok = "!=";
			break;
		case "/\\":
		case "\\land":
			tok = "&&";
			break;
		case "\\/":
		case "\\lor":
			tok = "||";
			break;
		case "=<":
		case "\\leq":
			tok = "<=";
			break;
		case "\\geq":
			tok = ">=";
			break;
		case "=":
			tok = "==";
			break;
		}

		Vector<Expression> toks = new Vector<Expression>();
		toks.add((Expression) leftRes.get(0));
		toks.add(new Token(" " + tok + " "));
		toks.add((Expression) rightRes.get(0));

		SimpleExpression comp = new SimpleExpression(toks);

		ret.add(comp);
		return ret;
	}

	public String toString() {
		return "PGoTLABoolOp (" + this.getLine() + "): (" + left.toString() + ") " + token
				+ " (" + right.toString() + ")";
	}
}
