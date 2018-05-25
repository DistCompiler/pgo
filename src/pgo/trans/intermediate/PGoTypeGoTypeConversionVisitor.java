package pgo.trans.intermediate;

import pgo.model.golang.Type;
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeChan;
import pgo.model.type.PGoTypeDecimal;
import pgo.model.type.PGoTypeFunction;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeMap;
import pgo.model.type.PGoTypeNatural;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSlice;
import pgo.model.type.PGoTypeString;
import pgo.model.type.PGoTypeTuple;
import pgo.model.type.PGoTypeUnrealizedNumber;
import pgo.model.type.PGoTypeUnrealizedTuple;
import pgo.model.type.PGoTypeVariable;
import pgo.model.type.PGoTypeVisitor;
import pgo.model.type.PGoTypeVoid;

public class PGoTypeGoTypeConversionVisitor extends PGoTypeVisitor<Type, RuntimeException> {

	@Override
	public Type visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeString pGoTypeString) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeNatural pGoTypeNatural) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Type visit(PGoTypeVoid pGoTypeVoid) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

}
