package pgo.model.golang;

import java.util.Objects;

/**
 * The for loop. Equivalent to PlusCal while
 *
 */
public class GoFor extends GoStatement {
	// boolean condition
	private final GoStatement init;
	private final GoExpression cond;
	private final GoStatement inc;

	private final GoBlock body;

	public GoFor(GoStatement init, GoExpression cond, GoStatement inc, GoBlock body) {
		this.init = init;
		this.cond = cond;
		this.inc = inc;
		this.body = body;
	}

	public GoStatement getInit() {
		return init;
	}
	
	public GoExpression getCondition() {
		return cond;
	}
	
	public GoStatement getIncrement() {
		return inc;
	}
	
	public GoBlock getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(GoStatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoFor aFor = (GoFor) o;
		return Objects.equals(init, aFor.init) &&
				Objects.equals(cond, aFor.cond) &&
				Objects.equals(inc, aFor.inc) &&
				Objects.equals(body, aFor.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(init, cond, inc, body);
	}
}
