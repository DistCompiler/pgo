package pgo.model.type;

import pgo.util.UnionFind;

import java.util.Map;

public class PGoTypeSubstitution {
	private final UnionFind<PGoTypeVariable> variableGroups;
	private final Map<PGoTypeVariable, PGoType> mapping;
	private final UnionFind<PGoTypeAbstractRecord> abstractRecordGroups;
	private final Map<PGoTypeAbstractRecord, RecordTypeEntry> abstractRecordsToEntries;

	public PGoTypeSubstitution(UnionFind<PGoTypeVariable> variableGroups, Map<PGoTypeVariable, PGoType> mapping,
	                           UnionFind<PGoTypeAbstractRecord> abstractRecordGroups,
	                           Map<PGoTypeAbstractRecord, RecordTypeEntry> abstractRecordsToEntries) {
		this.variableGroups = variableGroups;
		this.mapping = mapping;
		this.abstractRecordGroups = abstractRecordGroups;
		this.abstractRecordsToEntries = abstractRecordsToEntries;
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

	PGoTypeRecord substituteAbstractRecord(PGoTypeAbstractRecord pGoTypeAbstractRecord) {
		return abstractRecordsToEntries.get(abstractRecordGroups.find(pGoTypeAbstractRecord)).toConcreteRecord();
	}
}
