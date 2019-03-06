package pgo.model.type;

public class TypeHasVariableVisitor extends TypeVisitor<Boolean, RuntimeException> {
	private final TypeVariable typeVariable;

	public TypeHasVariableVisitor(TypeVariable typeVariable) {
		this.typeVariable = typeVariable;
	}

	@Override
	public Boolean visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(ArchetypeResourceType archetypeResourceType) throws RuntimeException {
		return archetypeResourceType.getReadType().accept(this) || archetypeResourceType.getWriteType().accept(this);
	}

	@Override
	public Boolean visit(ArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		return archetypeResourceCollectionType.getKeyType().accept(this) ||
				archetypeResourceCollectionType.getReadType().accept(this) ||
				archetypeResourceCollectionType.getWriteType().accept(this);
	}

	@Override
	public Boolean visit(TypeVariable typeVariable) throws RuntimeException {
			return typeVariable.equals(this.typeVariable);
	}

	@Override
	public Boolean visit(TupleType tupleType) throws RuntimeException {
		return tupleType.getElementTypes().stream().anyMatch(t -> t.accept(this));
	}

	@Override
	public Boolean visit(StringType stringType) throws RuntimeException {
        return false;
	}

	@Override
	public Boolean visit(SetType setType) throws RuntimeException {
        return setType.getElementType().accept(this);
	}

	@Override
	public Boolean visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		return nonEnumerableSetType.getElementType().accept(this);
	}

	@Override
	public Boolean visit(BoolType boolType) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(RealType realType) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(FunctionType functionType) throws RuntimeException {
		return functionType.getParamTypes().stream().anyMatch(p -> p.accept(this)) ||
				functionType.getReturnType().accept(this);
	}

	@Override
	public Boolean visit(ChanType chanType) throws RuntimeException {
		return chanType.getElementType().accept(this);
	}

	@Override
	public Boolean visit(IntType intType) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(InterfaceType interfaceType) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(MapType mapType) throws RuntimeException {
		return mapType.getKeyType().accept(this) || mapType.getValueType().accept(this);
	}

	@Override
	public Boolean visit(SliceType sliceType) throws RuntimeException {
		return sliceType.getElementType().accept(this);
	}

	@Override
	public Boolean visit(ProcedureType procedureType) throws RuntimeException {
		return procedureType.getParamTypes().stream().anyMatch(p -> p.accept(this));
	}

	@Override
	public Boolean visit(RecordType recordType) throws RuntimeException {
		return recordType.getFields().stream().anyMatch(f -> f.getType().accept(this));
	}
}
