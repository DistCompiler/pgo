package pgo.model.golang;

import java.util.Vector;

/**
 * The if statement
 *
 */
public class If extends Statement {
	// boolean condition
	private Expression cond;

	// true condition
	private Vector<Statement> thenS;

	// else
	private Vector<Statement> elseS;

	public If(Expression cond, Vector<Statement> thenS, Vector<Statement> elseS) {
		this.cond = cond;
		this.thenS = thenS;
		this.elseS = elseS;
	}

	public Expression getCond() {
		return cond;
	}

	public void setCond(Expression e) {
		this.cond = e;
	}

	public Vector<Statement> getThen() {
		return this.thenS;
	}

	public void setThen(Vector<Statement> e) {
		this.thenS = e;
	}

	public Vector<Statement> getElse() {
		return this.elseS;
	}

	public void setElse(Vector<Statement> e) {
		this.elseS = e;
	}

	@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> condStr = cond.toGo();
		ret.add("if " + String.join("; ", condStr) + " {");
		addIndented(ret, thenS);
		if (elseS.size() > 0) {
			ret.add("} else {");
			addIndented(ret, elseS);
		}
		ret.add("}");
		return ret;
	}
}
