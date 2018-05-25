package pgo.model.golang;

public abstract class TypeVisitor<T, E extends Throwable> {

	public abstract T visit(TypeName typeName) throws E;
	public abstract T visit(StructType structType) throws E;
	public abstract T visit(PtrType ptrType) throws E;
	public abstract T visit(SliceType sliceType) throws E;
	public abstract T visit(InterfaceType interfaceType) throws E;

}
