package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents an anonymous function in go
 *
 */
public class GoAnonymousFunction extends GoExpression {
	private List<GoFunctionArgument> arguments;
	private List<GoFunctionArgument> returnTypes;
	private GoBlock body;
	
	public GoAnonymousFunction(List<GoFunctionArgument> arguments, List<GoFunctionArgument> returnTypes, GoBlock body) {
		this.arguments = arguments;
		this.returnTypes = returnTypes;
		this.body = body;
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
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoAnonymousFunction that = (GoAnonymousFunction) o;
		return Objects.equals(arguments, that.arguments) &&
				Objects.equals(returnTypes, that.returnTypes) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(arguments, returnTypes, body);
	}
}