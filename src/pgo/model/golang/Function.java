package pgo.model.golang;

import java.util.List;

/**
 * Represents a function in go
 *
 */
public class Function {
	FunctionName name;
	
	List<Type> returnTypes;
	List<FunctionArgument> arguments;
	Block body;
	
	public Function(FunctionName name, List<FunctionArgument> arguments, List<Type> returnTypes, Block body) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public FunctionName getName() {
		return name;
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
}