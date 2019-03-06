package pgo.model.type;

import java.util.stream.Collectors;

public class TypeCopyVisitor extends TypeVisitor<Type, RuntimeException> {
	@Override
	public Type visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		return abstractRecordType;
	}

	@Override
	public Type visit(ArchetypeResourceType archetypeResourceType) throws RuntimeException {
		return new ArchetypeResourceType(
				archetypeResourceType.getReadType().accept(this),
				archetypeResourceType.getWriteType().accept(this),
				archetypeResourceType.getOrigins());
	}

	@Override
	public Type visit(ArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		return new ArchetypeResourceCollectionType(
				archetypeResourceCollectionType.getKeyType().accept(this),
				archetypeResourceCollectionType.getReadType().accept(this),
				archetypeResourceCollectionType.getWriteType().accept(this),
				archetypeResourceCollectionType.getOrigins());
	}

	@Override
	public Type visit(TypeVariable typeVariable) throws RuntimeException {
		return typeVariable;
	}

	@Override
	public Type visit(TupleType tupleType) throws RuntimeException {
		return new TupleType(
				tupleType.getElementTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()),
				tupleType.getOrigins());
	}

	@Override
	public Type visit(StringType stringType) throws RuntimeException {
		return stringType;
	}

	@Override
	public Type visit(SetType setType) throws RuntimeException {
		return new SetType(setType.getElementType().accept(this), setType.getOrigins());
	}

	@Override
	public Type visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		return new NonEnumerableSetType(
				nonEnumerableSetType.getElementType().accept(this), nonEnumerableSetType.getOrigins());
	}

	@Override
	public Type visit(BoolType boolType) throws RuntimeException {
		return boolType;
	}

	@Override
	public Type visit(RealType realType) throws RuntimeException {
		return realType;
	}

	@Override
	public Type visit(FunctionType functionType) throws RuntimeException {
		return new FunctionType(
				functionType.getParamTypes().stream().map(p -> p.accept(this)).collect(Collectors.toList()),
				functionType.getReturnType().accept(this),
				functionType.getOrigins());
	}

	@Override
	public Type visit(ChanType chanType) throws RuntimeException {
		return new ChanType(chanType.getElementType().accept(this), chanType.getOrigins());
	}

	@Override
	public Type visit(IntType intType) throws RuntimeException {
		return intType;
	}

	@Override
	public Type visit(InterfaceType interfaceType) throws RuntimeException {
		return interfaceType;
	}

	@Override
	public Type visit(MapType mapType) throws RuntimeException {
		return new MapType(
				mapType.getKeyType().accept(this),
				mapType.getValueType().accept(this),
				mapType.getOrigins());
	}

	@Override
	public Type visit(SliceType sliceType) throws RuntimeException {
		return new SliceType(sliceType.getElementType().accept(this), sliceType.getOrigins());
	}

	@Override
	public Type visit(ProcedureType procedureType) throws RuntimeException {
		return new ProcedureType(
				procedureType.getParamTypes().stream().map(p -> p.accept(this)).collect(Collectors.toList()),
				procedureType.getOrigins());
	}

	@Override
	public Type visit(RecordType recordType) throws RuntimeException {
		return new RecordType(
				recordType.getFields()
						.stream()
						.map(f -> new RecordType.Field(f.getName(), f.getType()))
						.collect(Collectors.toList()),
				recordType.getOrigins());
	}
}
