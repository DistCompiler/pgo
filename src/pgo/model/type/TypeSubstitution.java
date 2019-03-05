package pgo.model.type;

import pgo.util.UnionFind;

import java.util.Map;

public class TypeSubstitution {
	private final UnionFind<TypeVariable> variableGroups;
	private final Map<TypeVariable, Type> mapping;

	public TypeSubstitution(UnionFind<TypeVariable> variableGroups, Map<TypeVariable, Type> mapping) {
		this.variableGroups = variableGroups;
		this.mapping = mapping;
	}

	public boolean containsKey(TypeVariable v) {
		return mapping.containsKey(variableGroups.find(v));
	}

	public Type get(TypeVariable v) {
		return mapping.get(variableGroups.find(v));
	}

	public Type getOrDefault(TypeVariable v, Type t) {
		return mapping.getOrDefault(variableGroups.find(v), t);
	}
}
