package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * The for loop. Equivalent to PlusCal while
 *
 */
public class For extends Statement {
	// boolean condition
	private Expression cond;

	// inside of loop
	private List<Statement> then;

	public For(Expression cond, List<Statement> then) {
		this.cond = cond;
		this.then = then;
	}

	// an infinite loop in Go
	public For(List<Statement> then) {
		this.cond = null;
		this.then = then;
	}

	public Expression getCond() {
		return cond;
	}

	public void setCond(Expression e) {
		this.cond = e;
	}

	public List<Statement> getThen() {
		return this.then;
	}

	public void setThen(List<Statement> e) {
		this.then = e;
	}

	@Override
	public List<String> toGo() {
		List<String> ret = new Vector<>();
		List<String> conds = cond == null ? new Vector<>() : cond.toGo();
		ret.add("for " + String.join("; ", conds) + " {");
		addIndentedAST(ret, then);
		ret.add("}");
		return ret;
	}
}
