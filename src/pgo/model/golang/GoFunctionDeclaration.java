package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents a function in go
 *
 */
public class GoFunctionDeclaration extends GoDeclaration {
	private final String name;
	
	private GoFunctionParameter receiver;
	private final List<GoFunctionParameter> arguments;
	private final List<GoFunctionParameter> returnTypes;
	private final GoBlock body;
	
	public GoFunctionDeclaration(String name, GoFunctionParameter receiver, List<GoFunctionParameter> arguments, List<GoFunctionParameter> returnTypes, GoBlock body) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public String getName() {
		return name;
	}
	
	public GoFunctionParameter getReceiver() {
		return receiver;
	}
	
	public List<GoFunctionParameter> getReturnTypes(){
		return returnTypes;
	}
	
	public List<GoFunctionParameter> getArguments(){
		return arguments;
	}
	
	public GoBlock getBody() {
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(GoDeclarationVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoFunctionDeclaration that = (GoFunctionDeclaration) o;
		return Objects.equals(name, that.name) &&
				Objects.equals(receiver, that.receiver) &&
				Objects.equals(arguments, that.arguments) &&
				Objects.equals(returnTypes, that.returnTypes) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(name, receiver, arguments, returnTypes, body);
	}
}