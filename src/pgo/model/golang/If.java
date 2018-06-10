package pgo.model.golang;

import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		If anIf = (If) o;
		return Objects.equals(cond, anIf.cond) &&
				Objects.equals(bThen, anIf.bThen) &&
				Objects.equals(bElse, anIf.bElse);
	}

	@Override
	public int hashCode() {

		return Objects.hash(cond, bThen, bElse);
	}
}
