package pgo.trans.intermediate;

import java.util.Collections;

import pgo.model.golang.*;
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeChan;
import pgo.model.type.PGoTypeDecimal;
import pgo.model.type.PGoTypeFunction;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeProcedure;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSlice;
import pgo.model.type.PGoTypeString;
import pgo.model.type.PGoTypeTuple;
import pgo.model.type.PGoTypeUnrealizedNumber;
import pgo.model.type.PGoTypeUnrealizedTuple;
import pgo.model.type.PGoTypeVariable;
import pgo.model.type.PGoTypeVisitor;

public class PGoTypeGoTypeConversionVisitor extends PGoTypeVisitor<Type, RuntimeException> {

	@Override
	public Type visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public Type visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		return new SliceType(new InterfaceType(Collections.emptyList()));
	}

	@Override
	public Type visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return Builtins.String;
	}

	@Override
	public Type visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public Type visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new RuntimeException("internal compiler error");
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
		throw new RuntimeException("TODO");
	}

	@Override
	public Type visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new RuntimeException("TODO");
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
		throw new RuntimeException("TODO");
	}

}
