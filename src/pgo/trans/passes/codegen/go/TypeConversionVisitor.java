package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.GoBuiltins;
import pgo.model.golang.type.*;
import pgo.model.type.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class TypeConversionVisitor extends TypeVisitor<GoType, RuntimeException> {
	@Override
	public GoType visit(AbstractRecordType abstractRecordType) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoType visit(ArchetypeResourceType archetypeResourceType) throws RuntimeException {
		return new GoArchetypeResourceType(
				archetypeResourceType.getReadType().accept(this),
				archetypeResourceType.getWriteType().accept(this));
	}

	@Override
	public GoType visit(ArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		return new GoArchetypeResourceCollectionType(
				archetypeResourceCollectionType.getKeyType().accept(this),
				archetypeResourceCollectionType.getReadType().accept(this),
				archetypeResourceCollectionType.getWriteType().accept(this));
	}

	@Override
	public GoType visit(TypeVariable typeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoType visit(TupleType tupleType) throws RuntimeException {
		List<GoStructTypeField> fields = new ArrayList<>();
		List<Type> eTypes = tupleType.getElementTypes();
		for(int i = 0; i < eTypes.size(); ++i){
			fields.add(new GoStructTypeField("e"+i, eTypes.get(i).accept(this)));
		}
		return new GoStructType(fields);
	}

	@Override
	public GoType visit(StringType stringType) throws RuntimeException {
		return GoBuiltins.String;
	}

	@Override
	public GoType visit(SetType setType) throws RuntimeException {
		return new GoSliceType(setType.getElementType().accept(this));
	}

	@Override
	public GoType visit(NonEnumerableSetType nonEnumerableSetType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoType visit(BoolType boolType) throws RuntimeException {
		return GoBuiltins.Bool;
	}

	@Override
	public GoType visit(RealType realType) throws RuntimeException {
		return GoBuiltins.Float64;
	}

	@Override
	public GoType visit(FunctionType functionType) throws RuntimeException {
		List<Type> pTypes = functionType.getParamTypes();
		GoType keyType;
		if(pTypes.size() == 1){
			keyType = pTypes.get(0).accept(this);
		}else {
			keyType = new TupleType(pTypes, functionType.getOrigins()).accept(this);
		}
		return new GoSliceType(new GoStructType(Arrays.asList(
				new GoStructTypeField("key", keyType),
				new GoStructTypeField("value", functionType.getReturnType().accept(this)))));
	}

	@Override
	public GoType visit(ChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoType visit(IntType intType) throws RuntimeException {
		return GoBuiltins.Int;
	}

	@Override
	public GoType visit(InterfaceType interfaceType) throws RuntimeException {
		return GoBuiltins.Interface;
	}

	@Override
	public GoType visit(MapType mapType) throws RuntimeException {
		return new GoSliceType(new GoStructType(Arrays.asList(
				new GoStructTypeField("key", mapType.getKeyType().accept(this)),
				new GoStructTypeField("value", mapType.getValueType().accept(this)))));
	}

	@Override
	public GoType visit(SliceType sliceType) throws RuntimeException {
		return new GoSliceType(sliceType.getElementType().accept(this));
	}

	@Override
	public GoType visit(ProcedureType procedureType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoType visit(RecordType recordType) throws RuntimeException {
		// if the type of a variable is inferred to be a TLA+ record, use a map[string]interface{}
		// to represent it. This avoids issues around sending and receiving of these variables
		// through different archetype resources (e.g., RPC-based) and wrong casts
		// when we cannot infer the correct type of the message on the receiving end
		return new GoMapType(GoBuiltins.String, GoBuiltins.Interface);
	}
}
