package pgo.parser;

import java.util.HashMap;
import java.util.Map;

public class VariableMap {

	private final Map<Variable, Object> implementation;

	public VariableMap(){
		this.implementation = new HashMap<>();
	}

	public <Type> Type get(Variable<Type> k) {
		return (Type)implementation.get(k);
	}

	public <Type> VariableMap put(Variable<Type> k, Type v) {
		implementation.put(k, v);
		return this;
	}

}
