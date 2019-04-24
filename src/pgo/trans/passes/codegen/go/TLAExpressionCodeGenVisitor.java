package pgo.trans.passes.codegen.go;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoAnonymousFunctionBuilder;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoStructType;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.*;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class TLAExpressionCodeGenVisitor extends TLAExpressionVisitor<GoExpression, RuntimeException> {
	private GoBlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, Type> typeMap;
	private LocalVariableStrategy localStrategy;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionCodeGenVisitor(GoBlockBuilder builder, DefinitionRegistry registry, Map<UID, Type> typeMap,
									   LocalVariableStrategy localStrategy, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.localStrategy = localStrategy;
		this.globalStrategy = globalStrategy;
	}

	private List<GoExpression> evaluateQuantifierBoundSets(List<TLAQuantifierBound> bounds) {
		List<GoExpression> sets = new ArrayList<>();
		for(TLAQuantifierBound qb : bounds) {
			sets.add(qb.getSet().accept(this));
		}
		return sets;
	}

	private static GoType getFunctionKeyType(GoType fnType) {
		GoType keyValuePairType = ((GoSliceType)fnType).getElementType();
		return ((GoStructType)keyValuePairType).getFields().get(0).getType();
	}

	private void unfoldQuantifierBounds(List<TLAQuantifierBound> bounds, Consumer<GoBlockBuilder> action) {
		unfoldQuantifierBounds(bounds, evaluateQuantifierBoundSets(bounds), action);
	}

	private void unfoldQuantifierBounds(List<TLAQuantifierBound> bounds, List<GoExpression> evaluatedSets, Consumer<GoBlockBuilder> action) {
		GoBlockBuilder currentBuilder = builder;
		List<GoBlockBuilder> accumulatedBuilders = new ArrayList<>();
		for (int i = 0; i < bounds.size(); ++i) {
			GoExpression set = evaluatedSets.get(i);
			TLAQuantifierBound bound = bounds.get(i);
			GoForRangeBuilder forRangeBuilder = currentBuilder.forRange(set);

			if (bound.getType() == TLAQuantifierBound.Type.TUPLE) {
				GoVariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				currentBuilder = forRangeBuilder.getBlockBuilder();

				// useful for some internal codegen, not needed by user code
				currentBuilder.linkUID(bound.getUID(), v);

				List<TLAIdentifier> ids = bound.getIds();
				for(int j = 0; j < ids.size(); ++j) {
					GoVariableName name = currentBuilder.varDecl(ids.get(j).getId(), new GoIndexExpression(v, new GoIntLiteral(j)));
					currentBuilder.linkUID(ids.get(j).getUID(), name);
				}
			} else {
				if (bound.getIds().size() != 1) {
					throw new TODO();
				}

				TLAIdentifier id = bound.getIds().get(0);
				GoVariableName name = forRangeBuilder.initVariables(Arrays.asList("_", id.getId())).get(1);
				currentBuilder.linkUID(id.getUID(), name);
				// useful for some internal codegen, not needed by user code
				currentBuilder.linkUID(bound.getUID(), name);

				currentBuilder = forRangeBuilder.getBlockBuilder();
			}
			accumulatedBuilders.add(currentBuilder);
		}
		action.accept(currentBuilder);
		for (int i = accumulatedBuilders.size() - 1; i >= 0; i--) {
			accumulatedBuilders.get(i).close();
		}
	}

	@Override
	public GoExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		if (typeMap.get(tlaFunctionCall.getFunction().getUID()) instanceof ArchetypeResourceCollectionType) {
			return globalStrategy.readArchetypeResource(builder, tlaFunctionCall);
		}

		Type type = typeMap.get(tlaFunctionCall.getFunction().getUID());
		if (type instanceof MapType) {
			builder.addImport("sort");
			GoExpression function = tlaFunctionCall.getFunction().accept(this);
			List<GoExpression> params = new ArrayList<>();
			for(TLAExpression param : tlaFunctionCall.getParams()) {
				params.add(param.accept(this));
			}

			GoType keyType = getFunctionKeyType(type.accept(new TypeConversionVisitor()));
			GoVariableName key;
			if (tlaFunctionCall.getParams().size() == 1) {
				key = builder.varDecl("key", params.get(0));
			} else{
				if (keyType instanceof GoSliceType) {
					GoType elementType = ((GoSliceType)keyType).getElementType();
					key = builder.varDecl("key", new GoSliceLiteral(elementType, params));
				} else if (keyType instanceof GoStructType) {
					List<GoStructLiteralField> fields = new ArrayList<>();
					for(GoExpression param : params) {
						fields.add(new GoStructLiteralField(null, param));
					}
					key = builder.varDecl("key", new GoStructLiteral(keyType, fields));
				} else {
					throw new InternalCompilerError();
				}
			}

			GoAnonymousFunctionBuilder comparatorBuilder = builder.anonymousFunction();
			GoVariableName i = comparatorBuilder.addArgument("i", GoBuiltins.Int);
			comparatorBuilder.addReturn(GoBuiltins.Bool);
			try (GoBlockBuilder comparatorBody = comparatorBuilder.getBlockBuilder()) {
				comparatorBody.addStatement(
						new GoReturn(Collections.singletonList(
								new GoUnary(
										GoUnary.Operation.NOT,
										keyType.accept(new LessThanCodeGenVisitor(
												comparatorBody,
												new GoSelectorExpression(new GoIndexExpression(function, i), "key"),
												key))))));
			}
			GoVariableName index = builder.varDecl("index", new GoCall(
					new GoSelectorExpression(new GoVariableName("sort"), "Search"),
					Arrays.asList(
							new GoCall(new GoVariableName("len"), Collections.singletonList(function)),
							comparatorBuilder.getFunction())));
			return new GoSelectorExpression(new GoIndexExpression(function, index), "value");
		} else if (type instanceof SliceType) {
			if (tlaFunctionCall.getParams().size() != 1) {
				throw new InternalCompilerError(); // slices fundamentally cannot be indexed by multiple parameters
			}
			return new GoIndexExpression(
					tlaFunctionCall.getFunction().accept(this),
					new GoBinop(
							GoBinop.Operation.MINUS,
							tlaFunctionCall.getParams().get(0).accept(this),
							new GoIntLiteral(1)));
		} else{
			throw new InternalCompilerError();
		}
	}

	@Override
	public GoExpression visit(TLABinOp tlaBinOp) throws RuntimeException {
		UID ref = registry.followReference(tlaBinOp.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.generateGo(
				builder, tlaBinOp, registry,
				Arrays.asList(
						tlaBinOp.getLHS(),
						tlaBinOp.getRHS()),
				typeMap,
				localStrategy,
				globalStrategy);
	}

	@Override
	public GoExpression visit(TLABool tlaBool) throws RuntimeException {
		return tlaBool.getValue() ? GoBuiltins.True : GoBuiltins.False;
	}

	@Override
	public GoExpression visit(TLACase tlaCase) throws RuntimeException {
		UID uid = tlaCase.getArms().get(0).getResult().getUID();
		GoVariableName result = builder.varDecl("result", typeMap.get(uid).accept(new TypeConversionVisitor()));
		GoLabelName matched = builder.newLabel("matched");

		for (TLACaseArm caseArm : tlaCase.getArms()) {
			try (GoIfBuilder ifBuilder = builder.ifStmt(caseArm.getCondition().accept(this))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(result, caseArm.getResult().accept(this));
					yes.goTo(matched);
				}
			}
		}

		if (tlaCase.getOther() == null) {
			builder.addPanic(new GoStringLiteral("No matching case!"));
		} else {
			builder.assign(result, tlaCase.getOther().accept(this));
		}

		builder.label(matched);

		return result;
	}

	@Override
	public GoExpression visit(TLADot tlaDot) throws RuntimeException {
		Type expressionType = typeMap.get(tlaDot.getExpression().getUID());
		if (!(expressionType instanceof RecordType)) {
			throw new TODO();
		}

		RecordType mapType = (RecordType) expressionType;
		Type fieldType;

		Optional<RecordType.Field> field = mapType
				.getFields()
				.stream()
				.filter(f -> f.getName().equals(tlaDot.getField()))
				.findFirst();

		if (field.isPresent()) {
			fieldType = field.get().getType();
		} else {
			throw new InternalCompilerError();
		}

		GoType castType = fieldType.accept(new TypeConversionVisitor());
		GoExpression mapGet = new GoIndexExpression(
				tlaDot.getExpression().accept(this),
				new GoStringLiteral(tlaDot.getField())
		);

		if (castType.equals(GoBuiltins.Interface)) {
			return mapGet;
		} else {
			return new GoTypeCast(new GoTypeName(castType.toString()), mapGet);
		}
	}

	@Override
	public GoExpression visit(TLAExistential tlaExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAFunction tlaFunction) throws RuntimeException {
		GoType mapType = typeMap.get(tlaFunction.getUID()).accept(new TypeConversionVisitor());
		GoExpression capacity = null;
		List<TLAQuantifierBound> args = tlaFunction.getArguments();
		List<GoExpression> domains = evaluateQuantifierBoundSets(args);
		for(int argPos = 0; argPos < args.size(); ++argPos) {
			GoExpression domain = domains.get(argPos);
			GoExpression currentTerm = new GoCall(new GoVariableName("len"), Collections.singletonList(domain));
			if (capacity == null) {
				capacity = currentTerm;
			} else {
				capacity = new GoBinop(GoBinop.Operation.TIMES, capacity, currentTerm);
			}
		}
		GoVariableName function = builder.varDecl("function", new GoMakeExpression(mapType, new GoIntLiteral(0), capacity));
		unfoldQuantifierBounds(tlaFunction.getArguments(), domains, innerBuilder -> {
			GoType keyValuePairType = ((GoSliceType)mapType).getElementType();
			GoExpression key;
			if (args.size() == 1) {
				key = innerBuilder.findUID(args.get(0).getUID());
			} else{
				GoType keyType = ((GoStructType)keyValuePairType).getFields().get(0).getType();
				List<GoStructLiteralField> keyFields = new ArrayList<>();
				for(TLAQuantifierBound qb : args) {
					keyFields.add(new GoStructLiteralField(null, innerBuilder.findUID(qb.getUID())));
				}
				key = new GoStructLiteral(keyType, keyFields);
			}
			GoExpression value = tlaFunction.getBody().accept(
					new TLAExpressionCodeGenVisitor(innerBuilder, registry, typeMap, localStrategy, globalStrategy));
			GoExpression keyValuePair = new GoStructLiteral(keyValuePairType, Arrays.asList(
					new GoStructLiteralField("key", key),
					new GoStructLiteralField("value", value)
			));
			innerBuilder.assign(function, new GoCall(new GoVariableName("append"), Arrays.asList(function, keyValuePair)));
		});
		return function;
	}

	@Override
	public GoExpression visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAIf tlaIf) throws RuntimeException {
		GoVariableName result = builder.varDecl("result", typeMap.get(tlaIf.getTval().getUID()).accept(new TypeConversionVisitor()));
		try (GoIfBuilder ifBuilder = builder.ifStmt(tlaIf.getCond().accept(this))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.assign(result, tlaIf.getTval().accept(this));
				try (GoBlockBuilder no = ifBuilder.whenFalse()) {
					no.assign(result, tlaIf.getFval().accept(this));
				}
			}
		}
		return result;
	}

	@Override
	public GoExpression visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID ref = registry.followReference(tlaGeneralIdentifier.getUID());
		if (registry.isGlobalVariable(ref)) {
			return globalStrategy.readGlobalVariable(builder, ref);
		}
		if (typeMap.get(ref) instanceof ArchetypeResourceType) {
			return globalStrategy.readArchetypeResource(builder, tlaGeneralIdentifier);
		}
		if (typeMap.get(ref) instanceof ArchetypeResourceCollectionType) {
			return builder.findUID(ref);
		}
		if (registry.isLocalVariable(ref)) {
			return localStrategy.readLocalVariable(builder, ref);
		}
		if (registry.isConstant(ref)) {
			return builder.findUID(ref);
		}
		return registry.findOperator(ref).generateGo(
				builder, tlaGeneralIdentifier, registry, Collections.emptyList(), typeMap, localStrategy, globalStrategy);
	}

	@Override
	public GoExpression visit(TLATuple tlaTuple) throws RuntimeException {
		GoType sliceType = typeMap.get(tlaTuple.getUID()).accept(new TypeConversionVisitor());
		List<GoExpression> elements = new ArrayList<>();
		for (TLAExpression element : tlaTuple.getElements()) {
			elements.add(element.accept(this));
		}
		return sliceType.accept(new TLATupleCodeGenVisitor(elements));
	}

	@Override
	public GoExpression visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLANumber tlaNumber) throws RuntimeException {
		return new GoIntLiteral(Integer.valueOf(tlaNumber.getVal()));
	}

	@Override
	public GoExpression visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(tlaOperatorCall.getName().getUID()))
				.generateGo(
						builder, tlaOperatorCall, registry,
						tlaOperatorCall.getArgs(),
						typeMap, localStrategy, globalStrategy);
	}

	@Override
	public GoExpression visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		GoLabelName labelName = builder.newLabel("yes");
		GoVariableName exists = builder.varDecl("exists", GoBuiltins.False);
		unfoldQuantifierBounds(tlaQuantifiedExistential.getIds(), innerBlock -> {
			// needs a new visitor because we must write to the inner block rather than the outer block
			try (GoIfBuilder ifBuilder = innerBlock.ifStmt(tlaQuantifiedExistential.getBody()
					.accept(new TLAExpressionCodeGenVisitor(innerBlock, registry, typeMap, localStrategy, globalStrategy)))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(exists, GoBuiltins.True);
					if (tlaQuantifiedExistential.getIds().size() == 1) {
						yes.addStatement(new GoBreak());
					} else {
						yes.goTo(labelName);
					}
				}
			}
		});
		if (tlaQuantifiedExistential.getIds().size() != 1) {
			builder.label(labelName);
		}
		return exists;
	}

	@Override
	public GoExpression visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		GoLabelName labelName = builder.newLabel("no");
		GoVariableName forAll = builder.varDecl("forAll", GoBuiltins.True);
		unfoldQuantifierBounds(tlaQuantifiedUniversal.getIds(), innerBlock -> {
			// needs a new visitor because we must write to the inner block rather than the outer block
			try (GoIfBuilder ifBuilder = innerBlock.ifStmt(CodeGenUtil.invertCondition(
					innerBlock, registry, typeMap, localStrategy, globalStrategy, tlaQuantifiedUniversal.getBody()))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(forAll, GoBuiltins.False);
					if (tlaQuantifiedUniversal.getIds().size() == 1) {
						yes.addStatement(new GoBreak());
					} else {
						yes.goTo(labelName);
					}
				}
			}
		});
		if (tlaQuantifiedUniversal.getIds().size() != 1) {
			builder.label(labelName);
		}
		return forAll;
	}

	@Override
	public GoExpression visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		Map<GoExpression, GoExpression> kv = new HashMap<>();
		tlaRecordConstructor.getFields().forEach(f ->
				kv.put(new GoStringLiteral(f.getName().getId()), f.getValue().accept(this)));

		return new GoMapLiteral(GoBuiltins.String, GoBuiltins.Interface, kv);
	}

	@Override
	public GoExpression visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(tlaSetConstructor.getUID()));
		GoSliceLiteral result = new GoSliceLiteral(
				elementType,
				tlaSetConstructor.getContents().stream()
						.map(e -> e.accept(this))
						.collect(Collectors.toList()));
		if (tlaSetConstructor.getContents().size() <= 1) {
			// single-element or empty sets don't need any sorting or deduplication
			return result;
		} else {
			if (result.accept(new GoExpressionIsConstantVisitor())) {
				return CodeGenUtil.staticallySortSlice(result);
			}
			GoVariableName tmpSet = builder.varDecl("tmpSet", result);
			TLABuiltins.ensureUniqueSorted(builder, elementType, tmpSet);
			return tmpSet;
		}
	}

	@Override
	public GoExpression visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(tlaSetComprehension.getUID()));
		GoVariableName accumulator = builder.varDecl(
				"tmpSet", new GoMakeExpression(new GoSliceType(elementType), new GoIntLiteral(0), null));
		unfoldQuantifierBounds(tlaSetComprehension.getBounds(), innerBuilder -> {
			GoExpression body = tlaSetComprehension.getBody().accept(new TLAExpressionCodeGenVisitor(
					innerBuilder, registry, typeMap, localStrategy, globalStrategy));
			innerBuilder.assign(accumulator, new GoCall(new GoVariableName("append"), Arrays.asList(accumulator, body)));
		});
		TLABuiltins.ensureUniqueSorted(builder, elementType, accumulator);
		return accumulator;
	}

	@Override
	public GoExpression visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(tlaSetRefinement.getUID()));
		// GoRoutineStatement code
		// tmpSet := make([]GoType, 0)
		// for _, v := range pGoTLASetRefinement.getFrom() {
		// 	if pGoTLASetRefinement.getWhen() {
		// 		tmpSet = append(tmpSet, v)
		// 	}
		// }
		GoVariableName tmpSet = builder.varDecl(
				"tmpSet", new GoMakeExpression(new GoSliceType(elementType), new GoIntLiteral(0), null));
		GoForRangeBuilder forRangeBuilder = builder.forRange(tlaSetRefinement.getFrom().accept(this));

		GoVariableName v;
		if (tlaSetRefinement.getIdent().isTuple()) {
			v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
		} else {
			TLAIdentifier id = tlaSetRefinement.getIdent().getId();
			GoVariableName name = forRangeBuilder.initVariables(Arrays.asList("_", id.getId())).get(1);
			v = name;
			builder.linkUID(id.getUID(), name);
		}

		try (GoBlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
			if (tlaSetRefinement.getIdent().isTuple()) {
				List<TLAIdentifier> ids = tlaSetRefinement.getIdent().getTuple();
				for(int i = 0; i < ids.size(); ++i) {
					GoVariableName elem = forBody.varDecl(ids.get(i).getId(), new GoIndexExpression(v, new GoIntLiteral(i)));
					forBody.linkUID(ids.get(i).getUID(), elem);
				}
			}

			try (GoIfBuilder ifBuilder = forBody.ifStmt(tlaSetRefinement.getWhen().accept(
					new TLAExpressionCodeGenVisitor(forBody, registry, typeMap, localStrategy, globalStrategy)))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(tmpSet, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSet, v)));
				}
			}
		}
		// no need to ensure uniqueness and sortedness, we're just removing elements
		return tmpSet;
	}

	@Override
	public GoExpression visit(TLAString tlaString) throws RuntimeException {
		return new GoStringLiteral(tlaString.getValue());
	}

	@Override
	public GoExpression visit(TLAUnary tlaUnary) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(tlaUnary.getOperation().getUID()))
				.generateGo(
						builder, tlaUnary, registry,
						Collections.singletonList(tlaUnary.getOperand()),
						typeMap, localStrategy, globalStrategy);
	}

	@Override
	public GoExpression visit(TLAUniversal tlaUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return typeMap.get(plusCalDefaultInitValue.getUID()).accept(new TypeDefaultValueVisitor());
	}

	@Override
	public GoExpression visit(TLAFairness fairness) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLARef tlaRef) throws RuntimeException {
		throw new TODO();
	}
}
