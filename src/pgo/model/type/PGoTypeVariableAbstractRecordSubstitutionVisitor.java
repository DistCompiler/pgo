package pgo.model.type;

class PGoTypeVariableAbstractRecordSubstitutionVisitor extends PGoTypeVariableSubstitutionVisitor {
	PGoTypeVariableAbstractRecordSubstitutionVisitor(PGoTypeSubstitution substitution) {
		super(substitution);
	}

	@Override
	public PGoType visit(PGoTypeAbstractRecord pGoTypeAbstractRecord) throws RuntimeException {
		return substitution.substituteAbstractRecord(pGoTypeAbstractRecord).accept(this);
	}
}
