package pgo.model.type;

public abstract class PGoTypeVisitor<T, E extends Throwable> {
	public abstract T visit(PGoTypeVariable pGoTypeVariable) throws E;
	public abstract T visit(PGoTypeTuple pGoTypeTuple) throws E;
	public abstract T visit(PGoTypeString pGoTypeString) throws E;
	public abstract T visit(PGoTypeSet pGoTypeSet) throws E;
	public abstract T visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws E;
	public abstract T visit(PGoTypeBool pGoTypeBool) throws E;
	public abstract T visit(PGoTypeReal pGoTypeReal) throws E;
	public abstract T visit(PGoTypeFunction pGoTypeFunction) throws E;
	public abstract T visit(PGoTypeChan pGoTypeChan) throws E;
	public abstract T visit(PGoTypeInt pGoTypeInt) throws E;
	public abstract T visit(PGoTypeInterface pGoTypeInterface) throws E;
	public abstract T visit(PGoTypeMap pGoTypeMap) throws E;
	public abstract T visit(PGoTypeSlice pGoTypeSlice) throws E;
	public abstract T visit(PGoTypeProcedure pGoTypeProcedure) throws E;
}
