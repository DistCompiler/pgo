package pgo.model.golang;

import java.util.Map;

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
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
