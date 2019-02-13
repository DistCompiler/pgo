package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.type.*;

import java.util.Collections;

public class PGoTypeGoTypeDefaultValueVisitor extends PGoTypeVisitor<GoExpression, RuntimeException> {
	@Override
	public GoExpression visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public GoExpression visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return new GoStringLiteral("");
	}

	@Override
	public GoExpression visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		return new GoSliceLiteral(
				pGoTypeSet.getElementType().accept(new PGoTypeGoTypeConversionVisitor()),
				Collections.emptyList());
	}

	@Override
	public GoExpression visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return GoBuiltins.False;
	}

	@Override
	public GoExpression visit(PGoTypeReal pGoTypeReal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return new GoIntLiteral(0);
	}

	@Override
	public GoExpression visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		throw new TODO();
	}
}
