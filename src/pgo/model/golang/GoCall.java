package pgo.model.golang;

import java.util.Objects;

/**
 * A goroutine call
 *
 */
public class GoCall extends Statement {

	private Expression target;

	public GoCall(Expression target) {
		this.target = target;
	}
	
	public Expression getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoCall goCall = (GoCall) o;
		return Objects.equals(target, goCall.target);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target);
	}
}
