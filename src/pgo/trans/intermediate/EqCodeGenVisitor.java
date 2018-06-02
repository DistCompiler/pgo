package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import pgo.model.golang.*;

public class EqCodeGenVisitor extends TypeVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private Expression lhs;
	private Expression rhs;
	private boolean invert;

	public EqCodeGenVisitor(BlockBuilder builder, Expression lhs, Expression rhs, boolean invert) {
		this.builder = builder;
		this.lhs = lhs;
		this.rhs = rhs;
		this.invert = invert;
	}

	@Override
	public Expression visit(TypeName typeName) throws RuntimeException {
		if(typeName.isBuiltin()) {
			return new Binop(invert ? Binop.Operation.NEQ : Binop.Operation.EQ, lhs, rhs);
		}
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(StructType structType) throws RuntimeException {
		List<Expression> memberEqs = new ArrayList<>();
		for(StructTypeField field : structType.getFields()) {
			memberEqs.add(field.getType().accept(new EqCodeGenVisitor(builder, lhs, rhs, invert)));
		}
		if(memberEqs.isEmpty()) {
			return invert ? Builtins.False : Builtins.True;
		}else {
			Expression result = memberEqs.get(0);
			for(int i = 1; i < memberEqs.size(); ++i) {
				result = new Binop(invert ? Binop.Operation.OR : Binop.Operation.AND, result, memberEqs.get(i));
			}
			return result;
		}
	}

	@Override
	public Expression visit(PtrType ptrType) throws RuntimeException {
		return ptrType.getPointee().accept(new EqCodeGenVisitor(
				builder,
				new Unary(Unary.Operation.DEREF, lhs),
				new Unary(Unary.Operation.DEREF, rhs), invert));
	}

	@Override
	public Expression visit(SliceType sliceType) throws RuntimeException {
		VariableName result = builder.varDecl(
				"eq",
				new Binop(
						Binop.Operation.EQ,
						new Call(new VariableName("len"), Collections.singletonList(lhs)),
						new Call(new VariableName("len"), Collections.singletonList(rhs))));
		try(IfBuilder shouldInspect = builder.ifStmt(result)){
			try(BlockBuilder inspect = shouldInspect.whenTrue()){
				ForStatementClauseBuilder loopBuilder = inspect.forLoopWithClauses();
				VariableName i = loopBuilder.initVariable("i", new IntLiteral(0));
				loopBuilder.setCondition(
						new Binop(
								Binop.Operation.LT,
								i,
								new Call(new VariableName("len"), Collections.singletonList(lhs))));
				loopBuilder.setInc(new IncDec(true, i));
				try(BlockBuilder loopBody = loopBuilder.getBlockBuilder()) {
					loopBody.assign(
							result,
							sliceType.getElementType().accept(
									new EqCodeGenVisitor(
											loopBody,
											new Index(lhs, i),
											new Index(rhs, i),
											false)));
					try(IfBuilder shouldTerminate = loopBody.ifStmt(new Unary(Unary.Operation.NOT, result))){
						try(BlockBuilder body = shouldTerminate.whenTrue()){
							body.addStatement(new Break());
						}
					}
				}
			}
		}

		if(invert) {
			return new Unary(Unary.Operation.NOT, result);
		}else {
			return result;
		}
	}

	@Override
	public Expression visit(ChanType chanType) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
