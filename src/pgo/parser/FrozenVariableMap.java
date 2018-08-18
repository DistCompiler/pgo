package pgo.parser;

import java.util.Map;
import java.util.Objects;

public final class FrozenVariableMap {
	private final Map<Variable, Object> implementation;
	private final int hashCode;

	public FrozenVariableMap(Map<Variable, Object> implementation) {
		this.implementation = implementation;
		this.hashCode = implementation.hashCode();
	}

	@SuppressWarnings("unchecked")
	public <Type> Type get(Variable<Type> k) {
		return (Type)implementation.get(k);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		FrozenVariableMap that = (FrozenVariableMap) o;
		return Objects.equals(implementation, that.implementation);
	}

	@Override
	public int hashCode() {
		return hashCode;
	}
}
