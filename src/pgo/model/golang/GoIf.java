package pgo.model.golang;

import java.util.Objects;

/**
 * The if statement
 *
 */
public class GoIf extends GoStatement {
	// boolean condition
	private GoExpression cond;
	private GoBlock bThen;
	private GoBlock bElse;

	public GoIf(GoExpression cond, GoBlock bThen, GoBlock bElse) {
		this.cond = cond;
		this.bThen = bThen;
		this.bElse = bElse;
	}

	public GoExpression getCond() {
		return cond;
	}

	public GoBlock getThen() {
		return bThen;
	}

	public GoBlock getElse() {
		return bElse;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoIf anIf = (GoIf) o;
		return Objects.equals(cond, anIf.cond) &&
				Objects.equals(bThen, anIf.bThen) &&
				Objects.equals(bElse, anIf.bElse);
	}

	@Override
	public int hashCode() {

		return Objects.hash(cond, bThen, bElse);
	}
}
