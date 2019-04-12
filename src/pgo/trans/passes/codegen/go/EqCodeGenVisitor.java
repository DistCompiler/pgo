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
	public GoExpression visit(GoArchetypeResourceType archetypeResourceType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoArchetypeResourceCollectionType archetypeResourceCollectionType) throws RuntimeException {
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

		if (invert) {
			return new GoUnary(GoUnary.Operation.NOT, result);
		} else {
			return result;
		}
	}

	@Override
	public GoExpression visit(GoChanType chanType) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(GoMapType mapType) throws RuntimeException {
		GoVariableName result = builder.varDecl(
				"eq",
				new GoBinop(
						GoBinop.Operation.EQ,
						new GoCall(new GoVariableName("len"), Collections.singletonList(lhs)),
						new GoCall(new GoVariableName("len"), Collections.singletonList(rhs))));
		try(GoIfBuilder shouldInspect = builder.ifStmt(result)) {
			try(GoBlockBuilder yes = shouldInspect.whenTrue()) {
				GoType keysType = new GoSliceType(mapType.getKeyType());
				GoType valuesType = new GoSliceType(mapType.getValueType());

				// extract lhs keys, sorted
				GoVariableName keysL = yes.varDecl("keysL", keysType);
				GoForRangeBuilder buildKeysL = yes.forRange(lhs);
				GoVariableName kL = buildKeysL.initVariables(Collections.singletonList("kL")).get(0);
				try(GoBlockBuilder body = buildKeysL.getBlockBuilder()) {
					body.assign(keysL, new GoCall(new GoVariableName("append"), Arrays.asList(keysL, kL)));
				}
				TLABuiltins.ensureSorted(yes, mapType.getKeyType(), keysL);

				// extract rhs keys, sorted
				GoVariableName keysR = yes.varDecl("keysR", keysType);
				GoForRangeBuilder buildKeysR = yes.forRange(lhs);
				GoVariableName kR = buildKeysR.initVariables(Collections.singletonList("kR")).get(0);
				try(GoBlockBuilder body = buildKeysR.getBlockBuilder()) {
					body.assign(keysR, new GoCall(new GoVariableName("append"), Arrays.asList(keysR, kR)));
				}
				TLABuiltins.ensureSorted(yes, mapType.getKeyType(), keysR);

				yes.assign(result, keysType.accept(new EqCodeGenVisitor(yes, keysL, keysR, false)));

				try(GoIfBuilder shouldInspectValues = yes.ifStmt(result)) {
					try(GoBlockBuilder yes2 = shouldInspectValues.whenTrue()) {
						// extract lhs values (in key order)
						GoVariableName valuesL = yes2.varDecl("valuesL", valuesType);
						GoForRangeBuilder buildValuesL = yes2.forRange(keysL);
						kL = buildValuesL.initVariables(Arrays.asList("_", "kL")).get(1);
						try(GoBlockBuilder body = buildValuesL.getBlockBuilder()) {
							body.assign(valuesL, new GoCall(
									new GoVariableName("append"),
									Arrays.asList(valuesL, new GoIndexExpression(lhs, kL))));
						}

						// extract rhs values (in key order)
						GoVariableName valuesR = yes2.varDecl("valuesR", valuesType);
						GoForRangeBuilder buildValuesR = yes2.forRange(keysR);
						kR = buildValuesR.initVariables(Arrays.asList("_", "kR")).get(1);
						try(GoBlockBuilder body = buildValuesR.getBlockBuilder()) {
							body.assign(valuesR, new GoCall(
									new GoVariableName("append"),
									Arrays.asList(valuesL, new GoIndexExpression(rhs, kR))));
						}

						yes2.assign(result, valuesType.accept(new EqCodeGenVisitor(yes2, valuesL, valuesR, false)));
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
	public GoExpression visit(GoInterfaceType interfaceType) throws RuntimeException {
		throw new TODO();
	}

}
