package pgo.model.tla;

public abstract class TLAExpressionVisitor<T, E extends Throwable>{
	public abstract T visit(TLAFunctionCall tlaFunctionCall) throws E;
	public abstract T visit(TLABinOp tlaBinOp) throws E;
	public abstract T visit(TLABool tlaBool) throws E;
	public abstract T visit(TLACase tlaCase) throws E;
	public abstract T visit(TLADot tlaDot) throws E;
	public abstract T visit(TLAExistential tlaExistential) throws E;
	public abstract T visit(TLAFairness tlaFairness) throws E;
	public abstract T visit(TLAFunction tlaFunction) throws E;
	public abstract T visit(TLAFunctionSet tlaFunctionSet) throws E;
	public abstract T visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws E;
	public abstract T visit(TLAIf tlaIf) throws E;
	public abstract T visit(TLALet tlaLet) throws E;
	public abstract T visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws E;
	public abstract T visit(TLATuple tlaTuple) throws E;
	public abstract T visit(TLAMaybeAction tlaMaybeAction) throws E;
	public abstract T visit(TLANumber tlaNumber) throws E;
	public abstract T visit(TLAOperatorCall tlaOperatorCall) throws E;
	public abstract T visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws E;
	public abstract T visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws E;
	public abstract T visit(TLARecordConstructor tlaRecordConstructor) throws E;
	public abstract T visit(TLARecordSet tlaRecordSet) throws E;
	public abstract T visit(TLARef tlaRef) throws E;
	public abstract T visit(TLARequiredAction tlaRequiredAction) throws E;
	public abstract T visit(TLASetConstructor tlaSetConstructor) throws E;
	public abstract T visit(TLASetComprehension tlaSetComprehension) throws E;
	public abstract T visit(TLASetRefinement tlaSetRefinement) throws E;
	public abstract T visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws E;
	public abstract T visit(TLASpecialVariableValue tlaSpecialVariableValue) throws E;
	public abstract T visit(TLAString tlaString) throws E;
	public abstract T visit(TLAUnary tlaUnary) throws E;
	public abstract T visit(TLAUniversal tlaUniversal) throws E;
	public abstract T visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws E;
}
