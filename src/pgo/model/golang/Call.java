package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class Call extends Expression {

	private Expression target;
	private List<Expression> arguments;
	private boolean ellipsis;

	public Call(Expression target, List<Expression> arguments) {
		this(target, arguments, false);
	}

	public Call(Expression target, List<Expression> arguments, boolean ellipsis) {
		this.target = target;
		this.arguments = arguments;
		this.ellipsis = ellipsis;
	}

	public Expression getTarget() {
		return target;
	}

	public List<Expression> getArguments(){
		return arguments;
	}

	public boolean hasEllipsis() {
		return ellipsis;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Call call = (Call) o;
		return ellipsis == call.ellipsis &&
				Objects.equals(target, call.target) &&
				Objects.equals(arguments, call.arguments);
	}

	@Override
	public int hashCode() {

		return Objects.hash(target, arguments, ellipsis);
	}
}
