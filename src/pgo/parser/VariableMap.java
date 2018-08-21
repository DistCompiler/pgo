package pgo.parser;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public final class VariableMap {

	private final Map<Variable, Object> implementation;

	public VariableMap(){
		this.implementation = new HashMap<>();
	}

	@SuppressWarnings("unchecked")
	public <Type> Type get(Variable<Type> k) {
		return (Type)implementation.get(k);
	}

	public <Type> VariableMap put(Variable<Type> k, Type v) {
		implementation.put(k, v);
		return this;
	}

	public FrozenVariableMap freeze() { return new FrozenVariableMap(implementation); }

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		VariableMap that = (VariableMap) o;
		return Objects.equals(implementation, that.implementation);
	}

	@Override
	public int hashCode() {
		return Objects.hash(implementation);
	}
}
