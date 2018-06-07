package pgo.model.golang;

import java.util.List;
import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		InterfaceTypeField that = (InterfaceTypeField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(arguments, that.arguments) &&
				Objects.equals(returnTypes, that.returnTypes);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, arguments, returnTypes);
	}
}
