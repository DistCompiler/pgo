package pgo.trans.intermediate;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForStatementClauseBuilder;
import pgo.model.golang.type.*;

import java.util.Collections;
import java.util.List;

public class LessThanCodeGenVisitor extends GoTypeVisitor<GoExpression, RuntimeException> {

	private GoBlockBuilder builder;
	private GoExpression lhs;
	private GoExpression rhs;

	public LessThanCodeGenVisitor(GoBlockBuilder builder, GoExpression lhs, GoExpression rhs) {
		this.builder = builder;
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public GoExpression visit(GoTypeName typeName) throws RuntimeException {
		if(typeName.isBuiltin()) {
			return new GoBinop(GoBinop.Operation.LT, lhs, rhs);
		}else {
			throw new TODO();
		}
	}

	private GoExpression constructStructComparison(int i, List<GoStructTypeField> fields){
		GoStructTypeField field = fields.get(i);
		if(fields.size() == i+1){
			return field.getType().accept(
					new LessThanCodeGenVisitor(
							builder,
							new GoSelectorExpression(lhs, field.getName()),
							new GoSelectorExpression(rhs, field.getName())));
		}else{
			return new GoBinop(GoBinop.Operation.OR,
					field.getType().accept(
						new LessThanCodeGenVisitor(
								builder,
								new GoSelectorExpression(lhs, field.getName()),
								new GoSelectorExpression(rhs, field.getName()))),
					new GoBinop(GoBinop.Operation.AND,
							field.getType().accept(new EqCodeGenVisitor(
									builder,
									new GoSelectorExpression(lhs, field.getName()),
									new GoSelectorExpression(rhs, field.getName()),
									false)),
							constructStructComparison(i+1, fields)));
		}
	}

	@Override
	public GoExpression visit(GoStructType structType) throws RuntimeException {
		return constructStructComparison(0, structType.getFields());
	}

	@Override
	public GoExpression visit(GoPtrType ptrType) throws RuntimeException {
		return ptrType.getPointee().accept(
				new LessThanCodeGenVisitor(
						builder,
						new GoUnary(GoUnary.Operation.DEREF, lhs),
						new GoUnary(GoUnary.Operation.DEREF, rhs)));
	}

	@Override
	public GoExpression visit(GoSliceType sliceType) throws RuntimeException {
		GoVariableName less = builder.varDecl("less", new GoBinop(
				GoBinop.Operation.LT,
				new GoCall(new GoVariableName("len"), Collections.singletonList(lhs)),
				new GoCall(new GoVariableName("len"), Collections.singletonList(rhs))));
		try(GoIfBuilder lengthEQ = builder.ifStmt(
				new GoBinop(
						GoBinop.Operation.EQ,
						new GoCall(new GoVariableName("len"), Collections.singletonList(lhs)),
						new GoCall(new GoVariableName("len"), Collections.singletonList(rhs))))){
			try(GoBlockBuilder yes = lengthEQ.whenTrue()){
				GoForStatementClauseBuilder loopBuilder = yes.forLoopWithClauses();
				GoVariableName i = loopBuilder.initVariable("i", new GoIntLiteral(0));
				loopBuilder.setCondition(
						new GoBinop(
								GoBinop.Operation.LT,
								i,
								new GoCall(new GoVariableName("len"), Collections.singletonList(lhs))));
				loopBuilder.setInc(new GoIncDec(true, i));
				try(GoBlockBuilder loopBody = loopBuilder.getBlockBuilder()){
					loopBody.assign(
							less,
							sliceType.getElementType().accept(
									new LessThanCodeGenVisitor(
											loopBody,
											new GoIndexExpression(lhs, i),
											new GoIndexExpression(rhs, i))));
					try(GoIfBuilder shouldStop = loopBody.ifStmt(
							sliceType.getElementType().accept(
									new EqCodeGenVisitor(loopBody, new GoIndexExpression(lhs, i), new GoIndexExpression(rhs, i), true)))){
						try(GoBlockBuilder body = shouldStop.whenTrue()){
							body.addStatement(new GoBreak());
						}
					}
				}
			}
		}
		return less;
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
