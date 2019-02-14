package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.GoBuiltins;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoStructType;
import pgo.model.golang.type.GoStructTypeField;
import pgo.model.golang.type.GoType;
import pgo.model.type.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class PGoTypeGoTypeConversionVisitor extends PGoTypeVisitor<GoType, RuntimeException> {
	@Override
	public GoType visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoType visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		List<GoStructTypeField> fields = new ArrayList<>();
		List<PGoType> eTypes = pGoTypeTuple.getElementTypes();
		for(int i = 0; i < eTypes.size(); ++i){
			fields.add(new GoStructTypeField("e"+i, eTypes.get(i).accept(this)));
		}
		return new GoStructType(fields);
	}

	@Override
	public GoType visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return GoBuiltins.String;
	}

	@Override
	public GoType visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		return new GoSliceType(pGoTypeSet.getElementType().accept(this));
	}

	@Override
	public GoType visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoType visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return GoBuiltins.Bool;
	}

	@Override
	public GoType visit(PGoTypeReal pGoTypeReal) throws RuntimeException {
		return GoBuiltins.Float64;
	}

	@Override
	public GoType visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		List<PGoType> pTypes = pGoTypeFunction.getParamTypes();
		GoType keyType;
		if(pTypes.size() == 1){
			keyType = pTypes.get(0).accept(this);
		}else {
			keyType = new PGoTypeTuple(pTypes, pGoTypeFunction.getOrigins()).accept(this);
		}
		return new GoSliceType(new GoStructType(Arrays.asList(
				new GoStructTypeField("key", keyType),
				new GoStructTypeField("value", pGoTypeFunction.getReturnType().accept(this)))));
	}

	@Override
	public GoType visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoType visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return GoBuiltins.Int;
	}

	@Override
	public GoType visit(PGoTypeInterface pGoTypeInterface) throws RuntimeException {
		return GoBuiltins.Interface;
	}

	@Override
	public GoType visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		return new GoSliceType(new GoStructType(Arrays.asList(
				new GoStructTypeField("key", pGoTypeMap.getKeyType().accept(this)),
				new GoStructTypeField("value", pGoTypeMap.getValueType().accept(this)))));
	}

	@Override
	public GoType visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		return new GoSliceType(pGoTypeSlice.getElementType().accept(this));
	}

	@Override
	public GoType visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		throw new TODO();
	}
}
