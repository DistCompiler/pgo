package pgo.model.golang.type;

import pgo.model.golang.GoFunctionParameter;
import pgo.model.golang.GoNode;
import pgo.model.golang.GoNodeVisitor;

import java.util.List;
import java.util.Objects;

public class GoInterfaceTypeField extends GoNode {
	
	private final String name;
	private final List<GoFunctionParameter> arguments;
	private final List<GoFunctionParameter> returnTypes;

	public GoInterfaceTypeField(String name, List<GoFunctionParameter> arguments, List<GoFunctionParameter> returnTypes) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
	}

	public String getName() {
		return name;
	}

	public List<GoFunctionParameter> getArguments() {
		return arguments;
	}

	public List<GoFunctionParameter> getReturnTypes() {
		return returnTypes;
	}

	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoInterfaceTypeField that = (GoInterfaceTypeField) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(arguments, that.arguments) &&
				Objects.equals(returnTypes, that.returnTypes);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, arguments, returnTypes);
	}
}
