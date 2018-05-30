package pgo.model.golang;

import java.util.List;

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
}
