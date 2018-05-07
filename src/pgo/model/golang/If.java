package pgo.model.golang;

import java.util.List;
import java.util.Vector;

/**
 * The if statement
 *
 */
public class If extends Statement {
	// boolean condition
	private Expression cond;

	// true condition
	private List<Statement> thenS;

	// else
	private List<Statement> elseS;

	private boolean negation;

	public If(Expression cond, List<Statement> thenS, List<Statement> elseS) {
		this.cond = cond;
		this.thenS = thenS;
		this.elseS = elseS;
		this.negation = false;
	}

	public Expression getCond() {
		return cond;
	}

	public void setCond(Expression e) {
		this.cond = e;
	}

	public void negate() { this.negation = true; }

	public List<Statement> getThen() {
		return this.thenS;
	}

	public void setThen(List<Statement> e) {
		this.thenS = e;
	}

	public List<Statement> getElse() {
		return this.elseS;
	}

	public void setElse(List<Statement> e) {
		this.elseS = e;
	}

	@Override
	public List<String> toGo() {
		Vector<String> ret = new Vector<>();
		List<String> condStr = cond.toGo();
		String ifStr = negation ? "if !" : "if ";

		if (cond instanceof AnonymousFunction) {
			// in this case we want each line of func on a separate line, and we don't need semicolons
			ret.add(ifStr + condStr.remove(0));
			ret.addAll(condStr);
			ret.set(ret.size()-1, ret.get(ret.size()-1) + " {");
		} else {
			ret.add(ifStr + String.join("; ", condStr) + " {");
		}
		addIndentedAST(ret, thenS);
		if (elseS.size() > 0) {
			ret.add("} else {");
			addIndentedAST(ret, elseS);
		}
		ret.add("}");
		return ret;
	}
}
