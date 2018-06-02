package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.Builtins;
import pgo.model.golang.Expression;
import pgo.model.golang.IntLiteral;
import pgo.model.type.*;

public class PGoTypeGoTypeDefaultValueVisitor extends PGoTypeVisitor<Expression, RuntimeException> {
	@Override
	public Expression visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Expression visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return Builtins.EmptyString;
	}

	@Override
	public Expression visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Expression visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Expression visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return Builtins.False;
	}

	@Override
	public Expression visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return new IntLiteral(0);
	}

	@Override
	public Expression visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		throw new TODO();
	}
}
