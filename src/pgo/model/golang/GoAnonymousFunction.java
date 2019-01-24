package pgo.model.golang;

import java.util.List;
import java.util.Objects;

/**
 * Represents an anonymous function in go
 *
 */
public class GoAnonymousFunction extends GoExpression {
	private final List<GoFunctionParameter> params;
	private final List<GoFunctionParameter> returnTypes;
	private final GoBlock body;

	public GoAnonymousFunction(List<GoFunctionParameter> params, List<GoFunctionParameter> returnTypes, GoBlock body) {
		this.params = params;
		this.returnTypes = returnTypes;
		this.body = body;
	}

	public List<GoFunctionParameter> getReturnTypes(){
		return returnTypes;
	}

	public List<GoFunctionParameter> getParams(){
		return params;
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
		return Objects.equals(params, that.params) &&
				Objects.equals(returnTypes, that.returnTypes) &&
				Objects.equals(body, that.body);
	}

	@Override
	public int hashCode() {

		return Objects.hash(params, returnTypes, body);
	}
}