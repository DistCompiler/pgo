package pgo.model.type;

import java.util.Set;

public class TypeVariableCollectionVisitor extends TypeVisitor<Void, RuntimeException> {
	private final Set<TypeVariable> output;

	public TypeVariableCollectionVisitor(Set<TypeVariable> output) {
		this.output = output;
	}

	@Override
	public Void visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TypeVariable typeVariable) throws RuntimeException {
		output.add(typeVariable);
		return null;
	}

	@Override
	public Void visit(TupleType tupleType) throws RuntimeException {
		for (Type elementType : tupleType.getElementTypes()) {
			elementType.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(StringType stringType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(SetType setType) throws RuntimeException {
		setType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		nonEnumerableSetType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(BoolType boolType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(RealType realType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(FunctionType functionType) throws RuntimeException {
		for (Type paramType : functionType.getParamTypes()) {
			paramType.accept(this);
		}
		functionType.getReturnType().accept(this);
		return null;
	}

	@Override
	public Void visit(ChanType chanType) throws RuntimeException {
		chanType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(IntType intType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(InterfaceType interfaceType) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(MapType mapType) throws RuntimeException {
		mapType.getKeyType().accept(this);
		mapType.getValueType().accept(this);
		return null;
	}

	@Override
	public Void visit(SliceType sliceType) throws RuntimeException {
		sliceType.getElementType().accept(this);
		return null;
	}

	@Override
	public Void visit(ProcedureType procedureType) throws RuntimeException {
		for (Type paramType : procedureType.getParamTypes()) {
			paramType.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(RecordType recordType) throws RuntimeException {
		for (RecordType.Field field : recordType.getFields()) {
			field.getType().accept(this);
		}
		return null;
	}
}
