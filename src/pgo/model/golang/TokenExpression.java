package pgo.model.golang;

import java.util.Vector;

/**
 * A collection of tokens as an expression, such as "var[2]" which is a
 * collection of a variable token, [ and ] accessor tokens, and a literal
 *
 */
public class TokenExpression extends Expression {

	// the tokens in this expression
	private Vector<Token> exps;

	public TokenExpression(Vector<Token> exps) {
		this.exps = exps;
	}

	public Vector<Token> getTokens() {
		return this.exps;
	}

	public void setExpressions(Vector<Token> exps) {
		this.exps = exps;
	}

	@Override
	public String toGoExpr() {
		StringBuilder s = new StringBuilder();
		for (Expression e : exps) {
			s.append(e.toGoExpr());
		}
		return s.toString().trim();
	}

}
