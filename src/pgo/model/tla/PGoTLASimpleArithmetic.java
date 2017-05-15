package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;
import pgo.trans.intermediate.PGoTransStageGoGen;

/**
 * Represents a simple arithmetic operation written in TLA
 * Don't need to care about order of operation, as the output go code, as long as
 * written equivalent to TLA+, will do order of operation
 *
 */
public class PGoTLASimpleArithmetic extends PGoTLA {

	// the arithmetic token
	private String token;

	// the left side
	private PGoTLA left;

	// the right side
	private PGoTLA right;

	public PGoTLASimpleArithmetic(String t, PGoTLA prev, PGoTLA next, int line) {
		super(line);
		token = t;
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
		Vector<Statement> ret = new Vector<>();

		Vector<Statement> leftRes = this.getLeft().toStatements();
		Vector<Statement> rightRes = this.getRight().toStatements();

		// arithmetic operations should just be a single SimpleExpression
		assert (leftRes.size() == 1);
		assert (rightRes.size() == 1);
		assert (leftRes.get(0) instanceof Expression);
		assert (rightRes.get(0) instanceof Expression);

		if (this.getToken().equals("^")) {
			// TODO (issue #22) we need to check which number type we are using and cast to/from
			// float64 if needed
			PGoTransStageGoGen.go.getImports().addImport("math");
			// imports
			Vector<Expression> params = new Vector<>();
			params.add((Expression) leftRes.get(0));
			params.add((Expression) rightRes.get(0));
			FunctionCall fc = new FunctionCall("math.Pow", params);
			ret.add(fc);
		} else {
			Vector<Expression> toks = new Vector<Expression>();
			toks.add((Expression) leftRes.get(0));

			toks.add(new Token(" " + this.getToken() + " "));
			toks.add((Expression) rightRes.get(0));

			SimpleExpression arith = new SimpleExpression(toks);

			ret.add(arith);
		}
		return ret;
	}

	public String toString() {
		return "PGoTLASimpArith (" + this.getLine() + "): (" + left.toString() + ") " + token
				+ " (" + right.toString() + ")";
	}
}
