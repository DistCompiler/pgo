package pgo.trans.intermediate;

import java.util.Collections;

import pgo.model.golang.Binop;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Break;
import pgo.model.golang.Call;
import pgo.model.golang.Expression;
import pgo.model.golang.ForStatementClauseBuilder;
import pgo.model.golang.IfBuilder;
import pgo.model.golang.IncDec;
import pgo.model.golang.Index;
import pgo.model.golang.IntLiteral;
import pgo.model.golang.InterfaceType;
import pgo.model.golang.PtrType;
import pgo.model.golang.Selector;
import pgo.model.golang.SliceType;
import pgo.model.golang.StructType;
import pgo.model.golang.StructTypeField;
import pgo.model.golang.TypeName;
import pgo.model.golang.TypeVisitor;
import pgo.model.golang.Unary;
import pgo.model.golang.VariableName;

public class LessThanCodeGenVisitor extends TypeVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private Expression lhs;
	private Expression rhs;

	public LessThanCodeGenVisitor(BlockBuilder builder, Expression lhs, Expression rhs) {
		this.builder = builder;
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public Expression visit(TypeName typeName) throws RuntimeException {
		if(typeName.isBuiltin()) {
			return new Binop(Binop.Operation.LT, lhs, rhs);
		}else {
			throw new RuntimeException("TODO");
		}
	}

	@Override
	public Expression visit(StructType structType) throws RuntimeException {
		if(structType.getFields().size() == 2) {
			StructTypeField key = structType.getFields().get(0);
			StructTypeField value = structType.getFields().get(1);
			if(key.getName().equals("key") && value.getName().equals("value")) {
				return key.getType().accept(
						new LessThanCodeGenVisitor(
								builder,
								new Selector(lhs, "key"),
								new Selector(rhs, "key")));
			}
		}
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PtrType ptrType) throws RuntimeException {
		return ptrType.getPointee().accept(
				new LessThanCodeGenVisitor(
						builder,
						new Unary(Unary.Operation.DEREF, lhs),
						new Unary(Unary.Operation.DEREF, rhs)));
	}

	@Override
	public Expression visit(SliceType sliceType) throws RuntimeException {
		VariableName less = builder.varDecl("less", new Binop(
				Binop.Operation.LT,
				new Call(new VariableName("len"), Collections.singletonList(lhs)),
				new Call(new VariableName("len"), Collections.singletonList(rhs))));
		try(IfBuilder lengthEQ = builder.ifStmt(
				new Binop(
						Binop.Operation.EQ,
						new Call(new VariableName("len"), Collections.singletonList(lhs)),
						new Call(new VariableName("len"), Collections.singletonList(rhs))))){
			try(BlockBuilder yes = lengthEQ.whenTrue()){
				ForStatementClauseBuilder loopBuilder = yes.forLoopWithClauses();
				VariableName i = loopBuilder.initVariable("i", new IntLiteral(0));
				loopBuilder.setCondition(
						new Binop(
								Binop.Operation.LT,
								i,
								new Call(new VariableName("len"), Collections.singletonList(lhs))));
				loopBuilder.setInc(new IncDec(true, i));
				try(BlockBuilder loopBody = loopBuilder.getBlockBuilder()){
					loopBody.assign(
							less,
							sliceType.getElementType().accept(
									new LessThanCodeGenVisitor(
											loopBody,
											new Index(lhs, i),
											new Index(rhs, i))));
					try(IfBuilder shouldStop = loopBody.ifStmt(less)){
						try(BlockBuilder body = shouldStop.whenTrue()){
							body.addStatement(new Break());
						}
					}
				}
			}
		}
		return less;
	}

	@Override
	public Expression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
