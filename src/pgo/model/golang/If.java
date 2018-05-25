package pgo.model.golang;

/**
 * The if statement
 *
 */
public class If extends Statement {
	// boolean condition
	private Expression cond;
	private Block bThen;
	private Block bElse;

	public If(Expression cond, Block bThen, Block bElse) {
		this.cond = cond;
		this.bThen = bThen;
		this.bElse = bElse;
	}

	public Expression getCond() {
		return cond;
	}
	
	public Block getThen() {
		return bThen;
	}
	
	public Block getElse() {
		return bElse;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	/*@Override
	public Vector<String> toGo() {
		Vector<String> ret = new Vector<String>();
		Vector<String> condStr = cond.toGo();
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
	}*/
}
