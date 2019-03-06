package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.type.*;

import java.util.Collections;

public class TypeDefaultValueVisitor extends TypeVisitor<GoExpression, RuntimeException> {
	@Override
	public GoExpression visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(ArchetypeResourceType archetypeResourceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(ArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TypeVariable typeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoExpression visit(TupleType tupleType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(StringType stringType) throws RuntimeException {
		return new GoStringLiteral("");
	}

	@Override
	public GoExpression visit(SetType setType) throws RuntimeException {
		return new GoSliceLiteral(
				setType.getElementType().accept(new TypeConversionVisitor()),
				Collections.emptyList());
	}

	@Override
	public GoExpression visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(BoolType boolType) throws RuntimeException {
		return GoBuiltins.False;
	}

	@Override
	public GoExpression visit(RealType realType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(FunctionType functionType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(ChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(IntType intType) throws RuntimeException {
		return new GoIntLiteral(0);
	}

	@Override
	public GoExpression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(MapType mapType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(SliceType sliceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(ProcedureType procedureType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(RecordType recordType) throws RuntimeException {
		throw new TODO();
	}
}
