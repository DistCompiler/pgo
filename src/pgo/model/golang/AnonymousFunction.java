package pgo.model.golang;

import java.util.List;

/**
 * Represents an anonymous function in go
 *
 */
public class AnonymousFunction extends Expression {
	private List<FunctionArgument> arguments;
	private List<FunctionArgument> returnTypes;
	private Block body;
	
	public AnonymousFunction(List<FunctionArgument> arguments, List<FunctionArgument> returnTypes, Block body) {
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public List<FunctionArgument> getReturnTypes(){
		return returnTypes;
	}
	
	public List<FunctionArgument> getArguments(){
		return arguments;
	}
	
	public Block getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}
}