package pgo.model.golang;

import java.util.List;

/**
 * Represents an anonymous function in go
 *
 */
public class AnonymousFunction extends Expression {
	List<Type> returnTypes;
	List<FunctionArgument> arguments;
	Block body;
	
	public AnonymousFunction(List<FunctionArgument> arguments, List<Type> returnTypes, Block body) {
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public List<Type> getReturnTypes(){
		return returnTypes;
	}
	
	public List<FunctionArgument> getArguments(){
		return arguments;
	}
	
	public Block getBody() {
		return body;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}
}