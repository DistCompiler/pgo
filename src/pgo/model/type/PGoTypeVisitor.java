package pgo.model.type;

public abstract class PGoTypeVisitor<T, E extends Throwable> {

	public abstract T visit(PGoTypeVariable pGoTypeVariable) throws E;
	public abstract T visit(PGoTypeTuple pGoTypeTuple) throws E;
	public abstract T visit(PGoTypeString pGoTypeString) throws E;
	public abstract T visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws E;
	public abstract T visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws E;
	public abstract T visit(PGoTypeSet pGoTypeSet) throws E;
	public abstract T visit(PGoTypeBool pGoTypeBool) throws E;
	public abstract T visit(PGoTypeDecimal pGoTypeDecimal) throws E;
	public abstract T visit(PGoTypeNatural pGoTypeNatural) throws E;
	public abstract T visit(PGoTypeFunction pGoTypeFunction) throws E;
	public abstract T visit(PGoTypeChan pGoTypeChan) throws E;
	public abstract T visit(PGoTypeInt pGoTypeInt) throws E;
	public abstract T visit(PGoTypeMap pGoTypeMap) throws E;
	public abstract T visit(PGoTypeSlice pGoTypeSlice) throws E;
	public abstract T visit(PGoTypeVoid pGoTypeVoid) throws E;

}
