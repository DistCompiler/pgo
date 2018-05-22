package pgo.model.tla;

public abstract class PGoTLANodeVisitor<T, E extends Throwable>{
	public abstract T visit(PGoTLAExpression pGoTLAExpression) throws E;
	public abstract T visit(PGoTLAUnit pGoTLAUnit) throws E;
	public abstract T visit(PGoTLACaseArm pGoTLACaseArm) throws E;
	public abstract T visit(PGoTLAOpDecl pGoTLAOpDecl) throws E;
	public abstract T visit(PGoTLASubstitutionKey pGoTLASubstitutionKey) throws E;
	public abstract T visit(PGoTLARecordSet.Field field) throws E;
	public abstract T visit(PGoTLARecordConstructor.Field field) throws E;
	public abstract T visit(PGoTLAQuantifierBound pGoTLAQuantifierBound) throws E;
	public abstract T visit(PGoTLAInstance.Remapping remapping) throws E;
	public abstract T visit(PGoTLAIdentifierOrTuple pGoTLAIdentifierOrTuple) throws E;
	public abstract T visit(PGoTLAIdentifier pGoTLAIdentifier) throws E;
	public abstract T visit(PGoTLAGeneralIdentifierPart pGoTLAGeneralIdentifierPart) throws E;
	public abstract T visit(PGoTLAFunctionSubstitutionPair pGoTLAFunctionSubstitutionPair) throws E;
	public abstract T visit(PGoTLASymbol pGoTLASymbol) throws E;
}