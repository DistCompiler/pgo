package pgo.model.type;

import pgo.util.UnionFind;

import java.util.Map;

class TypeVariableAbstractRecordSubstitutionVisitor extends TypeVariableSubstitutionVisitor {
	private final UnionFind<AbstractRecordType> abstractRecordGroups;
	private final Map<AbstractRecordType, RecordTypeEntry> abstractRecordsToEntries;

	TypeVariableAbstractRecordSubstitutionVisitor(
			TypeSubstitution substitution, UnionFind<AbstractRecordType> abstractRecordGroups,
			Map<AbstractRecordType, RecordTypeEntry> abstractRecordsToEntries) {
		super(substitution);
		this.abstractRecordGroups = abstractRecordGroups;
		this.abstractRecordsToEntries = abstractRecordsToEntries;
	}

	@Override
	public Type visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		return abstractRecordsToEntries.get(abstractRecordGroups.find(abstractRecordType))
				.toConcreteRecord()
				.accept(this);
	}
}
