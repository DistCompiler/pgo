package pgo.trans.intermediate;

import pgo.TODO;
import pgo.model.golang.GoBinop;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.GoExpression;
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

public class PGoTypeEqualityCodeGenVisitor extends PGoTypeVisitor<GoExpression, RuntimeException> {

	private GoBlockBuilder builder;
	private boolean neq;
	private DefinitionRegistry registry;
	private GoExpression lhs;
	private GoExpression rhs;

	public PGoTypeEqualityCodeGenVisitor(GoBlockBuilder builder, boolean neq, DefinitionRegistry registry, GoExpression lhs, GoExpression rhs) {
		this.builder = builder;
		this.neq = neq;
		this.registry = registry;
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public GoExpression visit(PGoTypeVariable pGoTypeVariable) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeTuple pGoTypeTuple) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeString pGoTypeString) throws RuntimeException {
		return new GoBinop(neq ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
	}

	@Override
	public GoExpression visit(PGoTypeUnrealizedNumber pGoTypeUnrealizedNumber) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeSet pGoTypeSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeNonEnumerableSet pGoTypeNonEnumerableSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PGoTypeBool pGoTypeBool) throws RuntimeException {
		return new GoBinop(neq ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
	}

	@Override
	public GoExpression visit(PGoTypeDecimal pGoTypeDecimal) throws RuntimeException {
		return new GoBinop(neq ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
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
		return new GoBinop(neq ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
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
