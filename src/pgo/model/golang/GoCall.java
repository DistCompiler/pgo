package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class GoCall extends GoExpression {

	private GoExpression target;
	private List<GoExpression> arguments;
	private boolean ellipsis;

	public GoCall(GoExpression target, List<GoExpression> arguments) {
		this(target, arguments, false);
	}

	public GoCall(GoExpression target, List<GoExpression> arguments, boolean ellipsis) {
		this.target = target;
		this.arguments = arguments;
		this.ellipsis = ellipsis;
	}

	public GoExpression getTarget() {
		return target;
	}

	public List<GoExpression> getArguments(){
		return arguments;
	}

	public boolean hasEllipsis() {
		return ellipsis;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoCall call = (GoCall) o;
		return ellipsis == call.ellipsis &&
				Objects.equals(target, call.target) &&
				Objects.equals(arguments, call.arguments);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, arguments, ellipsis);
	}
}
