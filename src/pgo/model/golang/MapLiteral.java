package pgo.model.golang;

import java.util.Map;
import java.util.Objects;

public class MapLiteral extends Expression {
	
	private Map<Expression, Expression> pairs;
	private Type keyType;
	private Type valueType;

	public MapLiteral(Type keyType, Type valueType, Map<Expression, Expression> pairs) {
		this.keyType = keyType;
		this.valueType = valueType;
		this.pairs = pairs;
	}
	
	public Map<Expression, Expression> getPairs(){
		return pairs;
	}
	
	public Type getKeyType() {
		return keyType;
	}
	
	public Type getValueType() {
		return valueType;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		MapLiteral that = (MapLiteral) o;
		return Objects.equals(pairs, that.pairs) &&
				Objects.equals(keyType, that.keyType) &&
				Objects.equals(valueType, that.valueType);
	}

	@Override
	public int hashCode() {

		return Objects.hash(pairs, keyType, valueType);
	}
}
