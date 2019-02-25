package pgo.model.type;

import pgo.util.UnionFind;

import java.util.Map;

class PGoTypeVariableAbstractRecordSubstitutionVisitor extends PGoTypeVariableSubstitutionVisitor {
	private final UnionFind<PGoTypeAbstractRecord> abstractRecordGroups;
	private final Map<PGoTypeAbstractRecord, RecordTypeEntry> abstractRecordsToEntries;

	PGoTypeVariableAbstractRecordSubstitutionVisitor(
			PGoTypeSubstitution substitution, UnionFind<PGoTypeAbstractRecord> abstractRecordGroups,
			Map<PGoTypeAbstractRecord, RecordTypeEntry> abstractRecordsToEntries) {
		super(substitution);
		this.abstractRecordGroups = abstractRecordGroups;
		this.abstractRecordsToEntries = abstractRecordsToEntries;
	}

	@Override
	public PGoType visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws RuntimeException {
		return abstractRecordsToEntries.get(abstractRecordGroups.find(pGoTypeAbstractRecord))
				.toConcreteRecord()
				.accept(this);
	}
}
