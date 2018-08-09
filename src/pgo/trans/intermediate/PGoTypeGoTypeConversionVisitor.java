package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoStructType;
import pgo.model.golang.type.GoStructTypeField;
import pgo.model.golang.type.GoType;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeChan;
import pgo.model.type.PGoTypeDecimal;
import pgo.model.type.PGoTypeFunction;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeMap;
import pgo.model.type.PGoTypeProcedure;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeNonEnumerableSet;
import pgo.model.type.PGoTypeSlice;
import pgo.model.type.PGoTypeString;
import pgo.model.type.PGoTypeTuple;
import pgo.model.type.PGoTypeUnrealizedNumber;
import pgo.model.type.PGoTypeVariable;
import pgo.model.type.PGoTypeVisitor;

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
	public GoType visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new InternalCompilerError();
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
	public GoType visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
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
