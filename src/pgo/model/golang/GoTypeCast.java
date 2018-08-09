package pgo.model.golang;

import pgo.model.golang.type.GoTypeName;

import java.util.Objects;

/**
 * Represents a type conversion e.g. float64(x).
 */
public class GoTypeCast extends GoExpression {
	GoTypeName typeName;
	GoExpression target;
	
	public GoTypeCast(GoTypeName typeName, GoExpression target) {
		this.typeName = typeName;
		this.target = target;
	}
	
	public GoTypeName getTypeName() {
		return typeName;
	}
	
	public GoExpression getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoTypeCast typeCast = (GoTypeCast) o;
		return Objects.equals(typeName, typeCast.typeName) &&
				Objects.equals(target, typeCast.target);
	}

	@Override
	public int hashCode() {

		return Objects.hash(typeName, target);
	}
}