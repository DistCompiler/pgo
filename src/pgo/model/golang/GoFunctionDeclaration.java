package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents a function in go
 *
 */
public class GoFunctionDeclaration extends GoDeclaration {
	private String name;
	
	private GoFunctionArgument receiver;
	private List<GoFunctionArgument> arguments;
	private List<GoFunctionArgument> returnTypes;
	private GoBlock body;
	
	public GoFunctionDeclaration(String name, GoFunctionArgument receiver, List<GoFunctionArgument> arguments, List<GoFunctionArgument> returnTypes, GoBlock body) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public String getName() {
		return name;
	}
	
	public GoFunctionArgument getReceiver() {
		return receiver;
	}
	
	public List<GoFunctionArgument> getReturnTypes(){
		return returnTypes;
	}
	
	public List<GoFunctionArgument> getArguments(){
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