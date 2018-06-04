package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.type.*;

public class PGoTypeGoTypeConversionVisitor extends PGoTypeVisitor<Type, RuntimeException> {

	@Override
	public Type visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Type visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		List<StructTypeField> fields = new ArrayList<>();
		List<PGoType> eTypes = pGoTypeTuple.getElementTypes();
		for(int i = 0; i < eTypes.size(); ++i){
			fields.add(new StructTypeField("e"+i, eTypes.get(i).accept(this)));
		}
		return new StructType(fields);
	}

	@Override
	public Type visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return Builtins.String;
	}

	@Override
	public Type visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Type visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Type visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		return new SliceType(pGoTypeSet.getElementType().accept(this));
	}

	@Override
	public Type visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return Builtins.Bool;
	}

	@Override
	public Type visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
		return Builtins.Float64;
	}

	@Override
	public Type visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		List<PGoType> pTypes = pGoTypeFunction.getParamTypes();
		Type keyType;
		if(pTypes.size() == 1){
			keyType = pTypes.get(0).accept(this);
		}else {
			keyType = new PGoTypeTuple(pTypes, pGoTypeFunction.getOrigins()).accept(this);
		}
		return new SliceType(new StructType(Arrays.asList(
				new StructTypeField("key", keyType),
				new StructTypeField("value", pGoTypeFunction.getReturnType().accept(this)))));
	}

	@Override
	public Type visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Type visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return Builtins.Int;
	}

	@Override
	public Type visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		return new SliceType(pGoTypeSlice.getElementType().accept(this));
	}

	@Override
	public Type visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		throw new TODO();
	}

}
