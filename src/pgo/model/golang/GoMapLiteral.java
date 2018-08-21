package pgo.model.golang;

import pgo.model.golang.type.GoType;

import java.util.Map;
import java.util.Objects;

public class GoMapLiteral extends GoExpression {
	
	private Map<GoExpression, GoExpression> pairs;
	private GoType keyType;
	private GoType valueType;

	public GoMapLiteral(GoType keyType, GoType valueType, Map<GoExpression, GoExpression> pairs) {
		this.keyType = keyType;
		this.valueType = valueType;
		this.pairs = pairs;
	}
	
	public Map<GoExpression, GoExpression> getPairs(){
		return pairs;
	}
	
	public GoType getKeyType() {
		return keyType;
	}
	
	public GoType getValueType() {
		return valueType;
	}

	@Override
	public <T, E extends Throwable> T accept(GoExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		GoMapLiteral that = (GoMapLiteral) o;
		return Objects.equals(pairs, that.pairs) &&
				Objects.equals(keyType, that.keyType) &&
				Objects.equals(valueType, that.valueType);
	}

	@Override
	public int hashCode() {

		return Objects.hash(pairs, keyType, valueType);
	}
}
