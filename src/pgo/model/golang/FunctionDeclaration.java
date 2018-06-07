package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents a function in go
 *
 */
public class FunctionDeclaration extends Declaration {
	private String name;
	
	private FunctionArgument receiver;
	private List<FunctionArgument> arguments;
	private List<FunctionArgument> returnTypes;
	private Block body;
	
	public FunctionDeclaration(String name, FunctionArgument receiver, List<FunctionArgument> arguments, List<FunctionArgument> returnTypes, Block body) {
		this.name = name;
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
	}
	
	public String getName() {
		return name;
	}
	
	public FunctionArgument getReceiver() {
		return receiver;
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
	public <T, E extends Throwable> T accept(DeclarationVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		FunctionDeclaration that = (FunctionDeclaration) o;
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