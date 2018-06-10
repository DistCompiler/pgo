package pgo.model.golang;

import java.util.List;
import java.util.Objects;

public class SliceLiteral extends Expression {
	private List<Expression> initializers;
	private Type elementType;

	public SliceLiteral(Type elementType, List<Expression> initializers) {
		this.elementType = elementType;
		this.initializers = initializers;
	}
	
	public Type getElementType() {
		return elementType;
	}
	
	public List<Expression> getInitializers(){
		return initializers;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		SliceLiteral that = (SliceLiteral) o;
		return Objects.equals(initializers, that.initializers) &&
				Objects.equals(elementType, that.elementType);
	}

	@Override
	public int hashCode() {

		return Objects.hash(initializers, elementType);
	}
}
