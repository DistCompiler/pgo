package pgo.trans.intermediate;

import java.util.Collections;
import java.util.List;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.type.MapType;

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
			throw new TODO();
		}
	}

	private Expression constructStructComparison(int i, List<StructTypeField> fields){
		StructTypeField field = fields.get(i);
		if(fields.size() == i+1){
			return field.getType().accept(
					new LessThanCodeGenVisitor(
							builder,
							new Selector(lhs, field.getName()),
							new Selector(rhs, field.getName())));
		}else{
			return new Binop(Binop.Operation.OR,
					field.getType().accept(
						new LessThanCodeGenVisitor(
								builder,
								new Selector(lhs, field.getName()),
								new Selector(rhs, field.getName()))),
					new Binop(Binop.Operation.AND,
							field.getType().accept(new EqCodeGenVisitor(
									builder,
									new Selector(lhs, field.getName()),
									new Selector(rhs, field.getName()),
									false)),
							constructStructComparison(i+1, fields)));
		}
	}

	@Override
	public Expression visit(StructType structType) throws RuntimeException {
		return constructStructComparison(0, structType.getFields());
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
					try(IfBuilder shouldStop = loopBody.ifStmt(
							sliceType.getElementType().accept(
									new EqCodeGenVisitor(loopBody, new Index(lhs, i), new Index(rhs, i), true)))){
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
	public Expression visit(ChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(MapType mapType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(InterfaceType interfaceType) throws RuntimeException {
		throw new TODO();
	}

}
