package pgo.model.type;

import java.util.stream.Collectors;

public class TypeVariableSubstitutionVisitor extends TypeVisitor<Type, RuntimeException> {
	protected final TypeSubstitution substitution;

	public TypeVariableSubstitutionVisitor(TypeSubstitution substitution) {
		this.substitution = substitution;
	}

	@Override
	public Type visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		return abstractRecordType;
	}

	@Override
	public Type visit(TypeVariable typeVariable) throws RuntimeException {
		Type old = typeVariable;
		Type sub = substitution.getOrDefault(typeVariable, typeVariable);
		while (!sub.equals(old)) {
			old = sub;
			sub = sub.accept(this);
		}
		return sub;
	}

	@Override
	public Type visit(TupleType tupleType) throws RuntimeException {
		tupleType.setElementTypes(
				tupleType.getElementTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		return tupleType;
	}

	@Override
	public Type visit(StringType stringType) throws RuntimeException {
		return stringType;
	}

	@Override
	public Type visit(SetType setType) throws RuntimeException {
		setType.setElementType(setType.getElementType().accept(this));
		return setType;
	}

	@Override
	public Type visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		nonEnumerableSetType.setElementType(nonEnumerableSetType.getElementType().accept(this));
		return nonEnumerableSetType;
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
		functionType.setParamTypes(
				functionType.getParamTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		functionType.setReturnType(functionType.getReturnType().accept(this));
		return functionType;
	}

	@Override
	public Type visit(ChanType chanType) throws RuntimeException {
		chanType.setElementType(chanType.getElementType().accept(this));
		return chanType;
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
		mapType.setKeyType(mapType.getKeyType().accept(this));
		mapType.setValueType(mapType.getValueType().accept(this));
		return mapType;
	}

	@Override
	public Type visit(SliceType sliceType) throws RuntimeException {
		sliceType.setElementType(sliceType.getElementType().accept(this));
		return sliceType;
	}

	@Override
	public Type visit(ProcedureType procedureType) throws RuntimeException {
		procedureType.setParamTypes(
				procedureType.getParamTypes().stream().map(t -> t.accept(this)).collect(Collectors.toList()));
		return procedureType;
	}

	@Override
	public Type visit(RecordType recordType) throws RuntimeException {
		recordType.setFields(
				recordType.getFields()
						.stream()
						.map(f -> new RecordType.Field(f.getName(), f.getType().accept(this)))
						.collect(Collectors.toList()));
		return recordType;
	}
}
