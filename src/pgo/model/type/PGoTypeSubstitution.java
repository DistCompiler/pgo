package pgo.model.type;

import pgo.util.UnionFind;

import java.util.Map;

public class PGoTypeSubstitution {
	private final UnionFind<PGoTypeVariable> variableGroups;
	private final Map<PGoTypeVariable, PGoType> mapping;

	public PGoTypeSubstitution(UnionFind<PGoTypeVariable> variableGroups, Map<PGoTypeVariable, PGoType> mapping) {
		this.variableGroups = variableGroups;
		this.mapping = mapping;
	}

	public boolean containsKey(PGoTypeVariable v) {
		return mapping.containsKey(variableGroups.find(v));
	}

	public PGoType get(PGoTypeVariable v) {
		return mapping.get(variableGroups.find(v));
	}

	public PGoType getOrDefault(PGoTypeVariable v, PGoType t) {
		return mapping.getOrDefault(variableGroups.find(v), t);
	}
}
