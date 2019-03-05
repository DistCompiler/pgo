package pgo.model.type;

import pgo.util.Origin;

import java.util.List;

/**
 * Represents a map.
 */
public class MapType extends Type {
	private Type keyType;
	private Type valueType;

	public MapType(Type keyType, Type valueType, List<Origin> origins) {
		super(origins);
		this.keyType = keyType;
		this.valueType = valueType;
	}

	void setKeyType(Type keyType) {
		this.keyType = keyType;
	}

	public Type getKeyType() {
		return keyType;
	}

	void setValueType(Type valueType) {
		this.valueType = valueType;
	}

	public Type getValueType() {
		return valueType;
	}

	@Override
	public int hashCode() {
		return keyType.hashCode() * 17 + valueType.hashCode() * 19 + 3;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof MapType)) {
			return false;
		}
		MapType other = (MapType) p;
		return keyType.equals(other.keyType) && valueType.equals(other.valueType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
