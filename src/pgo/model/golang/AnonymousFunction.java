package pgo.model.golang;

import java.util.List;
import java.util.Objects;

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

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		AnonymousFunction that = (AnonymousFunction) o;
		return Objects.equals(arguments, that.arguments) &&
				Objects.equals(returnTypes, that.returnTypes) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(arguments, returnTypes, body);
	}
}