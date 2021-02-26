package pgo.trans.passes.codegen.go;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.builder.GoForStatementClauseBuilder;
import pgo.model.golang.type.*;
import pgo.trans.intermediate.TLABuiltins;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class EqCodeGenVisitor extends GoTypeVisitor<GoExpression, RuntimeException> {

	private final GoBlockBuilder builder;
	private final GoExpression lhs;
	private final GoExpression rhs;
	private final boolean invert;

	public EqCodeGenVisitor(GoBlockBuilder builder, GoExpression lhs, GoExpression rhs, boolean invert) {
		this.builder = builder;
		this.lhs = lhs;
		this.rhs = rhs;
		this.invert = invert;
	}

	private GoExpression deepEqual() {
		builder.addImport("reflect");

		GoExpression eq = new GoCall(
				new GoSelectorExpression(new GoVariableName("reflect"), "DeepEqual"),
				Arrays.asList(lhs, rhs)
		);

		if (invert) {
			return new GoUnary(GoUnary.Operation.NOT, eq);
		}

		return eq;
	}

	@Override
	public GoExpression visit(GoTypeName typeName) throws RuntimeException {
		if(typeName.isBuiltin()) {
			return new GoBinop(invert ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
		}
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoArchetypeResourceType archetypeResourceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoStructType structType) throws RuntimeException {
		return deepEqual();
	}

	@Override
	public GoExpression visit(GoPtrType ptrType) throws RuntimeException {
		return ptrType.getPointee().accept(new EqCodeGenVisitor(
				builder,
				new GoUnary(GoUnary.Operation.DEREF, lhs),
				new GoUnary(GoUnary.Operation.DEREF, rhs), invert));
	}

	@Override
	public GoExpression visit(GoSliceType sliceType) throws RuntimeException {
		return deepEqual();
	}

	@Override
	public GoExpression visit(GoChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoMapType mapType) throws RuntimeException {
		return deepEqual();
	}

	@Override
	public GoExpression visit(GoInterfaceType interfaceType) throws RuntimeException {
		return deepEqual();
	}

}
