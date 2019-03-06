package pgo.model.golang.type;

import pgo.model.golang.GoPtrType;

public abstract class GoTypeVisitor<T, E extends Throwable> {
	public abstract T visit(GoChanType chanType) throws E;
	public abstract T visit(GoInterfaceType interfaceType) throws E;
	public abstract T visit(GoMapType mapType) throws E;
	public abstract T visit(GoPtrType ptrType) throws E;
	public abstract T visit(GoSliceType sliceType) throws E;
	public abstract T visit(GoStructType structType) throws E;
	public abstract T visit(GoTypeName typeName) throws E;
	public abstract T visit(GoArchetypeResourceType archetypeResourceType) throws E;
	public abstract T visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws E;
}
