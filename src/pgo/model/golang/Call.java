package pgo.model.golang;

import java.util.List;

public class Call extends Expression {
	
	Expression target;
	List<Expression> arguments;
	
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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
