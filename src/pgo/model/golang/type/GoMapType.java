package pgo.model.golang.type;

import java.util.Collections;
import java.util.Map;
import java.util.Objects;

public class GoMapType extends GoType {
	private GoType keyType;
	private GoType valueType;
	private Map<String, GoType> inferredTypes;

	public GoMapType(GoType keyType, GoType valueType, Map<String, GoType> inferredTypes) {
		this.keyType = keyType;
		this.valueType = valueType;
		this.inferredTypes = inferredTypes;
	}

	public GoMapType(GoType keyType, GoType valueType) {
		this(keyType, valueType, Collections.emptyMap());
	}

	public GoType getKeyType() {
		return keyType;
	}

	public GoType getValueType() {
		return valueType;
	}

	public Map<String, GoType> getInferredTypes() {
		return inferredTypes;
	}

	public boolean isRecord() {
		return !inferredTypes.isEmpty();
	}

	@Override
	public int hashCode() {
		return Objects.hash(keyType, valueType, inferredTypes);
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
		return Objects.equals(keyType, that.keyType) &&
				Objects.equals(valueType, that.valueType) &&
				Objects.equals(inferredTypes, that.getInferredTypes());
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
