package pgo.model.golang;

import java.util.Objects;

/**
 * Represents a type conversion e.g. float64(x).
 */
public class TypeCast extends Expression {
	TypeName typeName;
	Expression target;
	
	public TypeCast(TypeName typeName, Expression target) {
		this.typeName = typeName;
		this.target = target;
	}
	
	public TypeName getTypeName() {
		return typeName;
	}
	
	public Expression getTarget() {
		return target;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		TypeCast typeCast = (TypeCast) o;
		return Objects.equals(typeName, typeCast.typeName) &&
				Objects.equals(target, typeCast.target);
	}

	@Override
	public int hashCode() {

		return Objects.hash(typeName, target);
	}
}