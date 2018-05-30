package pgo.trans.intermediate;

import pgo.model.golang.Binop;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Expression;
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeChan;
import pgo.model.type.PGoTypeDecimal;
import pgo.model.type.PGoTypeFunction;
import pgo.model.type.PGoTypeInt;
import pgo.model.type.PGoTypeMap;
import pgo.model.type.PGoTypeProcedure;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSlice;
import pgo.model.type.PGoTypeString;
import pgo.model.type.PGoTypeTuple;
import pgo.model.type.PGoTypeUnrealizedNumber;
import pgo.model.type.PGoTypeUnrealizedTuple;
import pgo.model.type.PGoTypeVariable;
import pgo.model.type.PGoTypeVisitor;

public class PGoTypeEqualityCodeGenVisitor extends PGoTypeVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private boolean neq;
	private DefinitionRegistry registry;
	private Expression lhs;
	private Expression rhs;

	public PGoTypeEqualityCodeGenVisitor(BlockBuilder builder, boolean neq, DefinitionRegistry registry, Expression lhs, Expression rhs) {
		this.builder = builder;
		this.neq = neq;
		this.registry = registry;
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public Expression visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return new Binop(neq ? Binop.Operation.NEQ : Binop.Operation.EQ, lhs, rhs);
	}

	@Override
	public Expression visit(PGoTypeUnrealizedTuple pGoTypeUnrealizedTuple) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return new Binop(neq ? Binop.Operation.NEQ : Binop.Operation.EQ, lhs, rhs);
	}

	@Override
	public Expression visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
		return new Binop(neq ? Binop.Operation.NEQ : Binop.Operation.EQ, lhs, rhs);
	}

	@Override
	public Expression visit(PGoTypeFunction pGoTypeFunction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeChan pGoTypeChan) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeInt pGoTypeInt) throws RuntimeException {
		return new Binop(neq ? Binop.Operation.NEQ : Binop.Operation.EQ, lhs, rhs);
	}

	@Override
	public Expression visit(PGoTypeMap pGoTypeMap) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeSlice pGoTypeSlice) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTypeProcedure pGoTypeProcedure) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
