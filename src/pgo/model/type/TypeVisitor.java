package pgo.model.type;

public abstract class TypeVisitor<T, E extends Throwable> {
	public abstract T visit(AbstractRecordType abstractRecordType) throws E;
	public abstract T visit(BoolType boolType) throws E;
	public abstract T visit(ChanType chanType) throws E;
	public abstract T visit(FunctionType functionType) throws E;
	public abstract T visit(InterfaceType interfaceType) throws E;
	public abstract T visit(IntType intType) throws E;
	public abstract T visit(MapType mapType) throws E;
	public abstract T visit(NonEnumerableSetType nonEnumerableSetType) throws E;
	public abstract T visit(ProcedureType procedureType) throws E;
	public abstract T visit(RealType realType) throws E;
	public abstract T visit(RecordType recordType) throws E;
	public abstract T visit(SetType setType) throws E;
	public abstract T visit(SliceType sliceType) throws E;
	public abstract T visit(StringType stringType) throws E;
	public abstract T visit(TupleType tupleType) throws E;
	public abstract T visit(TypeVariable typeVariable) throws E;
}
