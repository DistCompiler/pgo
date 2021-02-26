package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.List;
import java.util.Objects;

public class GoSliceLiteral extends GoExpression {
	private final List<GoExpression> initializers;
	private final GoType elementType;

	public GoSliceLiteral(GoType elementType, List<GoExpression> initializers) {
		this.elementType = elementType;
		this.initializers = initializers;
	}
	
	public GoType getElementType() {
		return elementType;
	}
	
	public List<GoExpression> getInitializers(){
		return initializers;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoSliceLiteral that = (GoSliceLiteral) o;
		return Objects.equals(initializers, that.initializers) &&
				Objects.equals(elementType, that.elementType);
	}

	@Override
	public int hashCode() {

		return Objects.hash(initializers, elementType);
	}
}
