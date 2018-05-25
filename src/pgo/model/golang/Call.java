package pgo.model.golang;

import java.util.List;

public class Call extends Expression {
	
	private Expression target;
	private List<Expression> arguments;
	
	public Call(Expression target, List<Expression> arguments) {
		this.target = target;
		this.arguments = arguments;
	}
	
	public Expression getTarget() {
		return target;
	}
	
	public List<Expression> getArguments(){
		return arguments;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

}
