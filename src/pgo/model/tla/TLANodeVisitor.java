package pgo.model.tla;

public abstract class TLANodeVisitor<T, E extends Throwable>{
	public abstract T visit(TLAExpression TLAExpression) throws E;
	public abstract T visit(TLAUnit pGoTLAUnit) throws E;
	public abstract T visit(TLACaseArm TLACaseArm) throws E;
	public abstract T visit(TLAOpDecl pGoTLAOpDecl) throws E;
	public abstract T visit(TLASubstitutionKey pGoTLASubstitutionKey) throws E;
	public abstract T visit(TLARecordSet.Field field) throws E;
	public abstract T visit(TLARecordConstructor.Field field) throws E;
	public abstract T visit(TLAQuantifierBound pGoTLAQuantifierBound) throws E;
	public abstract T visit(TLAInstance.Remapping remapping) throws E;
	public abstract T visit(TLAIdentifierOrTuple pGoTLAIdentifierOrTuple) throws E;
	public abstract T visit(TLAIdentifier pGoTLAIdentifier) throws E;
	public abstract T visit(TLAGeneralIdentifierPart pGoTLAGeneralIdentifierPart) throws E;
	public abstract T visit(TLAFunctionSubstitutionPair pGoTLAFunctionSubstitutionPair) throws E;
	public abstract T visit(TLASymbol pGoTLASymbol) throws E;
}