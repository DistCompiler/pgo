package pgo.model.golang;

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
}