package pgo.model.golang;

import java.util.Objects;

/**
 * The for loop. Equivalent to PlusCal while
 *
 */
public class For extends Statement {
	// boolean condition
	private Statement init;
	private Expression cond;
	private Statement inc;

	private Block body;

	public For(Statement init, Expression cond, Statement inc, Block body) {
		this.init = init;
		this.cond = cond;
		this.inc = inc;
		this.body = body;
	}

	public Statement getInit() {
		return init;
	}
	
	public Expression getCondition() {
		return cond;
	}
	
	public Statement getIncrement() {
		return inc;
	}
	
	public Block getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		For aFor = (For) o;
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
