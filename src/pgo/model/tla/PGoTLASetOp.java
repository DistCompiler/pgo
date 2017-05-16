package pgo.model.tla;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;

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

	protected Vector<Statement> toStatements() {
		Vector<Statement> ret = new Vector<>();

		Vector<Statement> leftRes = this.getLeft().toStatements();
		Vector<Statement> rightRes = this.getRight().toStatements();

		// lhs and rhs should each be a single Expression
		assert (leftRes.size() == 1);
		assert (rightRes.size() == 1);
		assert (leftRes.get(0) instanceof Expression);
		assert (rightRes.get(0) instanceof Expression);

		Vector<Expression> lhs = new Vector<>();
		lhs.add((Expression) leftRes.get(0));
		Expression rightSet = (Expression) rightRes.get(0);

		Vector<Expression> exp = new Vector<>();
		String funcName = null;
		// Map the set operation to the mapset function. \\notin does not have a corresponding
		// function and is handled separately.
		switch (this.token) {
		case "\\cup":
		case "\\union":
			funcName = "Union";
			break;
		case "\\cap":
		case "\\intersect":
			funcName = "Intersect";
			break;
		case "\\in":
			funcName = "Contains";
			break;
		case "\\notin":
			funcName = "NotIn";
			break;
		case "\\subseteq":
			funcName = "IsSubset";
			break;
		case "\\":
			funcName = "Difference";
			break;
		default:
			assert false;
		}

		if (funcName.equals("NotIn")) {
			exp.add(new Token("!"));
			funcName = "Contains";
		}
		// rightSet is the object because lhs can be an element (e.g. in Contains)
		FunctionCall fc = new FunctionCall(funcName, lhs, rightSet);
		exp.add(fc);
		ret.add(new SimpleExpression(exp));
		return ret;
	}
	
	protected Set<String> getImports() {
		Set<String> ret = new HashSet<>();
		ret.add("mapset");
		ret.addAll(this.getLeft().getImports());
		ret.addAll(this.getRight().getImports());
		return ret;
	}

	public String toString() {
		return "PGoTLASetOp (" + this.getLine() + "): (" + left.toString() + ") " + token + " ("
				+ right.toString() + ")";
	}
}
