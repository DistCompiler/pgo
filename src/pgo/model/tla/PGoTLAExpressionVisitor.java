package pgo.model.tla;

public abstract class PGoTLAExpressionVisitor<T, E extends Throwable>{
	public abstract T visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws E;
	public abstract T visit(PGoTLABinOp pGoTLABinOp) throws E;
	public abstract T visit(PGoTLABool pGoTLABool) throws E;
	public abstract T visit(PGoTLACase pGoTLACase) throws E;
	public abstract T visit(PGoTLAExistential pGoTLAExistential) throws E;
	public abstract T visit(PGoTLAFunction pGoTLAFunction) throws E;
	public abstract T visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws E;
	public abstract T visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws E;
	public abstract T visit(PGoTLAIf pGoTLAIf) throws E;
	public abstract T visit(PGoTLALet pGoTLALet) throws E;
	public abstract T visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws E;
	public abstract T visit(PGoTLATuple pGoTLATuple) throws E;
	public abstract T visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws E;
	public abstract T visit(PGoTLANumber pGoTLANumber) throws E;
	public abstract T visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws E;
	public abstract T visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws E;
	public abstract T visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws E;
	public abstract T visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws E;
	public abstract T visit(PGoTLARecordSet pGoTLARecordSet) throws E;
	public abstract T visit(PGoTLARequiredAction pGoTLARequiredAction) throws E;
	public abstract T visit(PGoTLASetConstructor pGoTLASetConstructor) throws E;
	public abstract T visit(PGoTLASetComprehension pGoTLASetComprehension) throws E;
	public abstract T visit(PGoTLASetRefinement pGoTLASetRefinement) throws E;
	public abstract T visit(PGoTLAString pGoTLAString) throws E;
	public abstract T visit(PGoTLAUnary pGoTLAUnary) throws E;
	public abstract T visit(PGoTLAUniversal pGoTLAUniversal) throws E;
}
