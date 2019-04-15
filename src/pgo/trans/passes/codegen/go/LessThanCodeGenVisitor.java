package pgo.trans.passes.codegen.go;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.builder.GoForStatementClauseBuilder;
import pgo.model.golang.type.*;
import pgo.model.type.RecordType;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.TLABuiltins;

import java.util.*;
import java.util.function.Function;

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
		if (typeName.isBuiltin()) {
			return new GoBinop(GoBinop.Operation.LT, lhs, rhs);
		} else {
			throw new TODO();
		}
	}

	@Override
	public GoExpression visit(GoArchetypeResourceType archetypeResourceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
		throw new TODO();
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
				try(GoBlockBuilder loopBody = loopBuilder.getBlockBuilder()) {
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
		// only comparison of record types are supported
		if (!mapType.isRecord()) {
			throw new TODO();
		}

		// Go pseudo-code:
		//
		// less := false
		// for {
		//     // comparisons below in sorted order of keys (record entries)
		//
		//     if !(Eq(lhs[e_1].(valType_1), rhs[e_1].(valType_1)) {
		//         less = LessThan(lhs[e_1].(valType_1), rhs[e_1].(valType_1))
		//         break
		//     }
		//     ...
		//     if !(Eq(lhs[e_N].(valType_N), rhs[e_1].(valType_1)) {
		//         less = LessThan(lhs[e_1].(valType_1), rhs[e_1].(valType_1))
		//         break
		//     }
		//
		//     break
		// }
		// return less

		GoVariableName less = builder.varDecl("less", GoBuiltins.False);
		try (GoBlockBuilder forLoop = builder.forLoop(null)) {
			mapType.getInferredTypes().forEach((f, valType) -> {
				Function<GoExpression, GoExpression> extractValue = exp -> {
					GoExpression index = new GoIndexExpression(exp, new GoStringLiteral(f));
					return new GoTypeCast(new GoTypeName(valType.toString()), index);
				};

				GoExpression lhsVal = extractValue.apply(lhs);
				GoExpression rhsVal = extractValue.apply(rhs);

				GoExpression condition = valType.accept(new EqCodeGenVisitor(forLoop, lhsVal, rhsVal, true));
				try (GoIfBuilder notEq = forLoop.ifStmt(condition)) {
					try (GoBlockBuilder different = notEq.whenTrue()) {
						GoExpression lt = valType.accept(new LessThanCodeGenVisitor(different, lhsVal, rhsVal));
						different.assign(less, lt);
						different.addStatement(new GoBreak());
					}
				}
			});

			forLoop.addStatement(new GoBreak());
		}

		return less;
	}

	@Override
	public GoExpression visit(GoInterfaceType interfaceType) throws RuntimeException {
		throw new TODO();
	}
}
