package pgo.model.golang.type;

import pgo.model.golang.Type;
import pgo.model.golang.TypeVisitor;

import java.util.Objects;

public class MapType extends Type {
	private Type keyType;
	private Type valueType;

	public MapType(Type keyType, Type valueType) {
		this.keyType = keyType;
		this.valueType = valueType;
	}

	public Type getKeyType() {
		return keyType;
	}

	public Type getValueType() {
		return valueType;
	}

	@Override
	public int hashCode() {
		return Objects.hash(keyType, valueType);
	}

	@Override
	public boolean equals(Object other) {
		if (this == other) {
			return true;
		}
		if (other == null || getClass() != other.getClass()) {
			return false;
		}
		MapType that = (MapType) other;
		return Objects.equals(keyType, that.keyType) && Objects.equals(valueType, that.valueType);
	}

	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
