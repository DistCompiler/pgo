package pgo.model.golang;

import pgo.model.golang.type.MapType;

public abstract class TypeVisitor<T, E extends Throwable> {

	public abstract T visit(TypeName typeName) throws E;
	public abstract T visit(StructType structType) throws E;
	public abstract T visit(PtrType ptrType) throws E;
	public abstract T visit(SliceType sliceType) throws E;
	public abstract T visit(ChanType chanType) throws E;
	public abstract T visit(MapType mapType) throws E;
	public abstract T visit(InterfaceType interfaceType) throws E;

}
