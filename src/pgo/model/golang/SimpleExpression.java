package pgo.model.golang;

import java.util.Vector;

/**
 * A simple expression: a one line operation, like an assignment or function
 * call
 * 
 */
public class SimpleExpression extends Expression {

	// the tokens in this expression
	private Vector<Expression> exps;

	public SimpleExpression(Vector<Expression> exps) {
		this.exps = exps;
	}

	public Vector<Expression> getExpressions() {
		return this.exps;
	}

	public void setExpressions(Vector<Expression> exps) {
		this.exps = exps;
	}

	@Override
	public String toGoExpr() {
		StringBuilder s = new StringBuilder();
		for (Expression e : exps) {
			s.append(e.toGoExpr());
			s.append(" ");
		}
		return s.toString().trim();
	}

}