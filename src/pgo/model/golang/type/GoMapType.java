package pgo.model.golang.type;

import java.util.Objects;

public class GoMapType extends GoType {
	private GoType keyType;
	private GoType valueType;

	public GoMapType(GoType keyType, GoType valueType) {
		this.keyType = keyType;
		this.valueType = valueType;
	}

	public GoType getKeyType() {
		return keyType;
	}

	public GoType getValueType() {
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
		GoMapType that = (GoMapType) other;
		return Objects.equals(keyType, that.keyType) && Objects.equals(valueType, that.valueType);
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
