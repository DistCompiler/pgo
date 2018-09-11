package pgo.model.tla;

public abstract class TLAExpressionVisitor<T, E extends Throwable>{
	public abstract T visit(TLAFunctionCall pGoTLAFunctionCall) throws E;
	public abstract T visit(TLABinOp TLABinOp) throws E;
	public abstract T visit(TLABool TLABool) throws E;
	public abstract T visit(TLACase TLACase) throws E;
	public abstract T visit(TLAExistential TLAExistential) throws E;
	public abstract T visit(TLAFunction pGoTLAFunction) throws E;
	public abstract T visit(TLAFunctionSet pGoTLAFunctionSet) throws E;
	public abstract T visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws E;
	public abstract T visit(TLAIf pGoTLAIf) throws E;
	public abstract T visit(TLALet pGoTLALet) throws E;
	public abstract T visit(TLAGeneralIdentifier pGoTLAVariable) throws E;
	public abstract T visit(TLATuple pGoTLATuple) throws E;
	public abstract T visit(TLAMaybeAction pGoTLAMaybeAction) throws E;
	public abstract T visit(TLANumber pGoTLANumber) throws E;
	public abstract T visit(TLAOperatorCall pGoTLAOperatorCall) throws E;
	public abstract T visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws E;
	public abstract T visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws E;
	public abstract T visit(TLARecordConstructor pGoTLARecordConstructor) throws E;
	public abstract T visit(TLARecordSet pGoTLARecordSet) throws E;
	public abstract T visit(TLARequiredAction pGoTLARequiredAction) throws E;
	public abstract T visit(TLASetConstructor pGoTLASetConstructor) throws E;
	public abstract T visit(TLASetComprehension pGoTLASetComprehension) throws E;
	public abstract T visit(TLASetRefinement pGoTLASetRefinement) throws E;
	public abstract T visit(TLAString pGoTLAString) throws E;
	public abstract T visit(TLAUnary pGoTLAUnary) throws E;
	public abstract T visit(TLAUniversal pGoTLAUniversal) throws E;
	public abstract T visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws E;
	public abstract T visit(TLAFairness tlaFairness) throws E;
	public abstract T visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws E;
	public abstract T visit(TLASpecialVariableValue tlaSpecialVariableValue) throws E;
	public abstract T visit(TLARef tlaRef) throws E;
}
