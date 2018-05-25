package pgo.model.golang;

import java.util.List;

public class InterfaceTypeField extends Node {
	
	private String name;
	private List<FunctionArgument> arguments;
	private List<FunctionArgument> returnTypes;

	public InterfaceTypeField(String name, List<FunctionArgument> arguments, List<FunctionArgument> returnTypes) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
	}

	public String getName() {
		return name;
	}

	public List<FunctionArgument> getArguments() {
		return arguments;
	}

	public List<FunctionArgument> getReturnTypes() {
		return returnTypes;
	}

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
