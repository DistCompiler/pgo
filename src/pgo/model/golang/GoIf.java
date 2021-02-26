package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * The if statement
 *
 */
public class GoIf extends GoStatement {
	// boolean condition
	private final GoExpression cond;
	private final List<GoVariableName> initialVariables;
	private final GoExpression initialExpression;
	private final GoBlock bThen;
	private final GoBlock bElse;

	public GoIf(GoExpression cond, List<GoVariableName> initialVariables, GoExpression initialExpression, GoBlock bThen, GoBlock bElse) {
		this.cond = cond;
		this.initialVariables = initialVariables;
		this.initialExpression = initialExpression;
		this.bThen = bThen;
		this.bElse = bElse;
	}

	public GoExpression getCond() {
		return cond;
	}

	public List<GoVariableName> getInitialVariables() {
		return this.initialVariables;
	}

	public GoExpression getInitialExpression() {
		return this.initialExpression;
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
				Objects.equals(initialVariables, anIf.getInitialVariables()) &&
				Objects.equals(initialExpression, anIf.getInitialExpression()) &&
				Objects.equals(bThen, anIf.bThen) &&
				Objects.equals(bElse, anIf.bElse);
	}

	@Override
	public int hashCode() {
		return Objects.hash(cond, initialVariables, initialExpression, bThen, bElse);
	}
}
