package pgo.model.golang;

import java.util.Vector;

/**
 * The for loop. Equivalent to PlusCal while
 *
 */
public class For extends Statement {
	// boolean condition
	private Expression cond;

	// inside of loop
	private Vector<Statement> then;

	public For(Expression cond, Vector<Statement> then) {
		this.cond = cond;
		this.then = then;
	}

	public Expression getCond() {
		return cond;
	}

	public void setCond(Expression e) {
		this.cond = e;
	}

	public Vector<Statement> getThen() {
		return this.then;
	}

	public void setThen(Vector<Statement> e) {
		this.then = e;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> conds = cond.toGo();
		ret.add("for " + String.join("; ", conds) + " {");
		addIndented(ret, then, false);
		ret.add("}");
		return ret;
	}
}
