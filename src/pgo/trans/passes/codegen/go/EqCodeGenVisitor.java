package pgo.trans.passes.codegen.go;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForStatementClauseBuilder;
import pgo.model.golang.type.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class EqCodeGenVisitor extends GoTypeVisitor<GoExpression, RuntimeException> {

	private GoBlockBuilder builder;
	private GoExpression lhs;
	private GoExpression rhs;
	private boolean invert;

	public EqCodeGenVisitor(GoBlockBuilder builder, GoExpression lhs, GoExpression rhs, boolean invert) {
		this.builder = builder;
		this.lhs = lhs;
		this.rhs = rhs;
		this.invert = invert;
	}

	@Override
	public GoExpression visit(GoTypeName typeName) throws RuntimeException {
		if(typeName.isBuiltin()) {
			return new GoBinop(invert ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ, lhs, rhs);
		}
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoStructType structType) throws RuntimeException {
		List<GoExpression> memberEqs = new ArrayList<>();
		for(GoStructTypeField field : structType.getFields()) {
			memberEqs.add(field.getType().accept(new EqCodeGenVisitor(builder, lhs, rhs, invert)));
		}
		if(memberEqs.isEmpty()) {
			return invert ? GoBuiltins.False : GoBuiltins.True;
		}else {
			GoExpression result = memberEqs.get(0);
			for(int i = 1; i < memberEqs.size(); ++i) {
				result = new GoBinop(invert ? GoBinop.Operation.OR : GoBinop.Operation.AND, result, memberEqs.get(i));
			}
			return result;
		}
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
		// special-case nicer looking comparison when one slice is a literal
		boolean lhsIsConstant = lhs instanceof GoSliceLiteral;
		boolean rhsIsConstant = rhs instanceof GoSliceLiteral;
		if(lhsIsConstant || rhsIsConstant){
			GoExpression constant = lhsIsConstant ? lhs : rhs;
			GoExpression other = lhsIsConstant ? rhs : lhs;
			GoSliceLiteral constantSlice = (GoSliceLiteral)constant;
			GoExpression comparison = new GoBinop(
					invert ? GoBinop.Operation.NEQ : GoBinop.Operation.EQ,
					new GoCall(new GoVariableName("len"), Collections.singletonList(other)),
					new GoIntLiteral(constantSlice.getInitializers().size()));
			List<GoExpression> constantInitialisers = constantSlice.getInitializers();
			for (int i = 0; i < constantInitialisers.size(); ++i) {
				comparison = new GoBinop(invert ? GoBinop.Operation.OR : GoBinop.Operation.AND,
						comparison,
						sliceType.getElementType().accept(
								new EqCodeGenVisitor(
										builder,
										new GoIndexExpression(other, new GoIntLiteral(i)),
										constantInitialisers.get(i),
										invert)));
			}
			return comparison;
		}

		// general case long-form comparison
		GoVariableName result = builder.varDecl(
				"eq",
				new GoBinop(
						GoBinop.Operation.EQ,
						new GoCall(new GoVariableName("len"), Collections.singletonList(lhs)),
						new GoCall(new GoVariableName("len"), Collections.singletonList(rhs))));
		try(GoIfBuilder shouldInspect = builder.ifStmt(result)){
			try(GoBlockBuilder inspect = shouldInspect.whenTrue()){
				GoForStatementClauseBuilder loopBuilder = inspect.forLoopWithClauses();
				GoVariableName i = loopBuilder.initVariable("i", new GoIntLiteral(0));
				loopBuilder.setCondition(
						new GoBinop(
								GoBinop.Operation.LT,
								i,
								new GoCall(new GoVariableName("len"), Collections.singletonList(lhs))));
				loopBuilder.setInc(new GoIncDec(true, i));
				try(GoBlockBuilder loopBody = loopBuilder.getBlockBuilder()) {
					loopBody.assign(
							result,
							sliceType.getElementType().accept(
									new EqCodeGenVisitor(
											loopBody,
											new GoIndexExpression(lhs, i),
											new GoIndexExpression(rhs, i),
											false)));
					try(GoIfBuilder shouldTerminate = loopBody.ifStmt(new GoUnary(GoUnary.Operation.NOT, result))){
						try(GoBlockBuilder body = shouldTerminate.whenTrue()){
							body.addStatement(new GoBreak());
						}
					}
				}
			}
		}

		if(invert) {
			return new GoUnary(GoUnary.Operation.NOT, result);
		}else {
			return result;
		}
	}

	@Override
	public GoExpression visit(GoChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoMapType mapType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoInterfaceType interfaceType) throws RuntimeException {
		throw new TODO();
	}

}
