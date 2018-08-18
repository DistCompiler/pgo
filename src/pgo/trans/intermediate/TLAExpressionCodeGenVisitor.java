package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoAnonymousFunctionBuilder;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoForRangeBuilder;
import pgo.model.golang.type.GoSliceType;
import pgo.model.golang.type.GoStructType;
import pgo.model.golang.type.GoType;
import pgo.model.tla.*;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeMap;
import pgo.model.type.PGoTypeSlice;
import pgo.scope.UID;
import pgo.trans.passes.codegen.CodeGenUtil;
import pgo.trans.passes.codegen.GoExpressionIsConstantVisitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class TLAExpressionCodeGenVisitor extends TLAExpressionVisitor<GoExpression, RuntimeException> {
	private GoBlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionCodeGenVisitor(GoBlockBuilder builder, DefinitionRegistry registry, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	private List<GoExpression> evaluateQuantifierBoundSets(List<TLAQuantifierBound> bounds){
		List<GoExpression> sets = new ArrayList<>();
		for(TLAQuantifierBound qb : bounds){
			sets.add(qb.getSet().accept(this));
		}
		return sets;
	}

	private static GoType getFunctionKeyType(GoType fnType){
		GoType keyValuePairType = ((GoSliceType)fnType).getElementType();
		return ((GoStructType)keyValuePairType).getFields().get(0).getType();
	}

	private void unfoldQuantifierBounds(List<TLAQuantifierBound> bounds, Consumer<GoBlockBuilder> action){
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
			}else {
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
	public GoExpression visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		PGoType type = typeMap.get(pGoTLAFunctionCall.getFunction().getUID());
		if(type instanceof PGoTypeMap){
			builder.addImport("sort");
			GoExpression function = pGoTLAFunctionCall.getFunction().accept(this);
			List<GoExpression> params = new ArrayList<>();
			for(TLAExpression param : pGoTLAFunctionCall.getParams()){
				params.add(param.accept(this));
			}

			GoType keyType = getFunctionKeyType(type.accept(new PGoTypeGoTypeConversionVisitor()));
			GoVariableName key;
			if(pGoTLAFunctionCall.getParams().size() == 1){
				key = builder.varDecl("key", params.get(0));
			}else{
				if(keyType instanceof GoSliceType){
					GoType elementType = ((GoSliceType)keyType).getElementType();
					key = builder.varDecl("key", new GoSliceLiteral(elementType, params));
				}else if(keyType instanceof GoStructType){
					List<GoStructLiteralField> fields = new ArrayList<>();
					for(GoExpression param : params){
						fields.add(new GoStructLiteralField(null, param));
					}
					key = builder.varDecl("key", new GoStructLiteral(keyType, fields));
				}else {
					throw new InternalCompilerError();
				}
			}

			GoAnonymousFunctionBuilder comparatorBuilder = builder.anonymousFunction();
			GoVariableName i = comparatorBuilder.addArgument("i", GoBuiltins.Int);
			comparatorBuilder.addReturn(GoBuiltins.Bool);
			try(GoBlockBuilder comparatorBody = comparatorBuilder.getBlockBuilder()){
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
		}else if(type instanceof PGoTypeSlice){
			if (pGoTLAFunctionCall.getParams().size() != 1) {
				throw new InternalCompilerError(); // slices fundamentally cannot be indexed by multiple parameters
			}
			return new GoIndexExpression(
					pGoTLAFunctionCall.getFunction().accept(this),
					new GoBinop(
							GoBinop.Operation.MINUS,
							pGoTLAFunctionCall.getParams().get(0).accept(this),
							new GoIntLiteral(1)));
		}else{
			throw new InternalCompilerError();
		}
	}

	@Override
	public GoExpression visit(TLABinOp TLABinOp) throws RuntimeException {
		UID ref = registry.followReference(TLABinOp.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.generateGo(
				builder, TLABinOp, registry,
				Arrays.asList(
						TLABinOp.getLHS(),
						TLABinOp.getRHS()),
				typeMap,
				globalStrategy);
	}

	@Override
	public GoExpression visit(TLABool TLABool) throws RuntimeException {
		return TLABool.getValue() ? GoBuiltins.True : GoBuiltins.False;
	}

	@Override
	public GoExpression visit(TLACase pGoTLACase) throws RuntimeException {
		UID uid = pGoTLACase.getArms().get(0).getResult().getUID();
		GoVariableName result = builder.varDecl("result", typeMap.get(uid).accept(new PGoTypeGoTypeConversionVisitor()));
		GoLabelName matched = builder.newLabel("matched");

		for (TLACaseArm caseArm : pGoTLACase.getArms()) {
			try (GoIfBuilder ifBuilder = builder.ifStmt(caseArm.getCondition().accept(this))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(result, caseArm.getResult().accept(this));
					yes.goTo(matched);
				}
			}
		}

		if (pGoTLACase.getOther() == null) {
			builder.addPanic(new GoStringLiteral("No matching case!"));
		} else {
			builder.assign(result, pGoTLACase.getOther().accept(this));
		}

		builder.label(matched);

		return result;
	}

	@Override
	public GoExpression visit(TLAExistential TLAExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		GoType mapType = typeMap.get(pGoTLAFunction.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		GoExpression capacity = null;
		List<TLAQuantifierBound> args = pGoTLAFunction.getArguments();
		List<GoExpression> domains = evaluateQuantifierBoundSets(args);
		for(int argPos = 0; argPos < args.size(); ++argPos){
			GoExpression domain = domains.get(argPos);
			GoExpression currentTerm = new GoCall(new GoVariableName("len"), Collections.singletonList(domain));
			if(capacity == null){
				capacity = currentTerm;
			}else{
				capacity = new GoBinop(GoBinop.Operation.TIMES, capacity, currentTerm);
			}
		}
		GoVariableName function = builder.varDecl("function", new GoMakeExpression(mapType, new GoIntLiteral(0), capacity));
		unfoldQuantifierBounds(pGoTLAFunction.getArguments(), domains, innerBuilder -> {
			GoType keyValuePairType = ((GoSliceType)mapType).getElementType();
			GoExpression key;
			if(args.size() == 1){
				key = innerBuilder.findUID(args.get(0).getUID());
			}else{
				GoType keyType = ((GoStructType)keyValuePairType).getFields().get(0).getType();
				List<GoStructLiteralField> keyFields = new ArrayList<>();
				for(TLAQuantifierBound qb : args){
					keyFields.add(new GoStructLiteralField(null, innerBuilder.findUID(qb.getUID())));
				}
				key = new GoStructLiteral(keyType, keyFields);
			}
			GoExpression value = pGoTLAFunction.getBody().accept(
					new TLAExpressionCodeGenVisitor(innerBuilder, registry, typeMap, globalStrategy));
			GoExpression keyValuePair = new GoStructLiteral(keyValuePairType, Arrays.asList(
					new GoStructLiteralField("key", key),
					new GoStructLiteralField("value", value)
			));
			innerBuilder.assign(function, new GoCall(new GoVariableName("append"), Arrays.asList(function, keyValuePair)));
		});
		return function;
	}

	@Override
	public GoExpression visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAIf pGoTLAIf) throws RuntimeException {
		GoVariableName result = builder.varDecl("result", typeMap.get(pGoTLAIf.getTval().getUID()).accept(new PGoTypeGoTypeConversionVisitor()));
		try(GoIfBuilder ifBuilder = builder.ifStmt(pGoTLAIf.getCond().accept(this))) {
			try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
				yes.assign(result, pGoTLAIf.getTval().accept(this));
				try (GoBlockBuilder no = ifBuilder.whenFalse()) {
					no.assign(result, pGoTLAIf.getFval().accept(this));
				}
			}
		}
		return result;
	}

	@Override
	public GoExpression visit(TLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		UID ref = registry.followReference(pGoTLAVariable.getUID());
		if (registry.isGlobalVariable(ref)) {
			return globalStrategy.readGlobalVariable(builder, ref);
		}
		if (registry.isLocalVariable(ref)) {
			return builder.findUID(ref);
		}
		if (registry.isConstant(ref)) {
			return builder.findUID(ref);
		}
		return registry.findOperator(ref).generateGo(
				builder, pGoTLAVariable, registry, Collections.emptyList(), typeMap, globalStrategy);
	}

	@Override
	public GoExpression visit(TLATuple pGoTLATuple) throws RuntimeException {
		GoType sliceType = typeMap.get(pGoTLATuple.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		List<GoExpression> elements = new ArrayList<>();
		for (TLAExpression element : pGoTLATuple.getElements()) {
			elements.add(element.accept(this));
		}
		return sliceType.accept(new TLATupleCodeGenVisitor(builder, elements));
	}

	@Override
	public GoExpression visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLANumber pGoTLANumber) throws RuntimeException {
		return new GoIntLiteral(Integer.valueOf(pGoTLANumber.getVal()));
	}

	@Override
	public GoExpression visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLAOperatorCall.getName().getUID()))
				.generateGo(
						builder, pGoTLAOperatorCall, registry,
						pGoTLAOperatorCall.getArgs(),
						typeMap, globalStrategy);
	}

	@Override
	public GoExpression visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		GoLabelName labelName = builder.newLabel("yes");
		GoVariableName exists = builder.varDecl("exists", GoBuiltins.False);
		unfoldQuantifierBounds(pGoTLAQuantifiedExistential.getIds(), innerBlock -> {
			// needs a new visitor because we must write to the inner block rather than the outer block
			try (GoIfBuilder ifBuilder = innerBlock.ifStmt(pGoTLAQuantifiedExistential.getBody()
					.accept(new TLAExpressionCodeGenVisitor(innerBlock, registry, typeMap, globalStrategy)))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(exists, GoBuiltins.True);
					if(pGoTLAQuantifiedExistential.getIds().size() == 1) {
						yes.addStatement(new GoBreak());
					}else {
						yes.goTo(labelName);
					}
				}
			}
		});
		if(pGoTLAQuantifiedExistential.getIds().size() != 1) {
			builder.label(labelName);
		}
		return exists;
	}

	@Override
	public GoExpression visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetConstructor.getUID()));
		GoExpression result = new GoSliceLiteral(
				elementType,
				pGoTLASetConstructor.getContents().stream()
						.map(e -> e.accept(this))
						.collect(Collectors.toList()));
		if(pGoTLASetConstructor.getContents().size() <= 1) {
			// single-element or empty sets don't need any sorting or deduplication
			return result;
		}else {
			if(result.accept(new GoExpressionIsConstantVisitor())){
				return CodeGenUtil.staticallySortSlice((GoSliceLiteral)result);
			}
			GoVariableName tmpSet = builder.varDecl("tmpSet", result);
			TLABuiltins.ensureUniqueSorted(builder, elementType, tmpSet);
			return tmpSet;
		}
	}

	@Override
	public GoExpression visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetComprehension.getUID()));
		GoVariableName accumulator = builder.varDecl(
				"tmpSet", new GoMakeExpression(new GoSliceType(elementType), new GoIntLiteral(0), null));
		unfoldQuantifierBounds(pGoTLASetComprehension.getBounds(), innerBuilder -> {
			GoExpression body = pGoTLASetComprehension.getBody().accept(new TLAExpressionCodeGenVisitor(
					innerBuilder, registry, typeMap, globalStrategy));
			innerBuilder.assign(accumulator, new GoCall(new GoVariableName("append"), Arrays.asList(accumulator, body)));
		});
		TLABuiltins.ensureUniqueSorted(builder, elementType, accumulator);
		return accumulator;
	}

	@Override
	public GoExpression visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		GoType elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetRefinement.getUID()));
		// GoRoutineStatement code
		// tmpSet := make([]GoType, 0)
		// for _, v := range pGoTLASetRefinement.getFrom() {
		// 	if pGoTLASetRefinement.getWhen() {
		// 		tmpSet = append(tmpSet, v)
		// 	}
		// }
		GoVariableName tmpSet = builder.varDecl(
				"tmpSet", new GoMakeExpression(new GoSliceType(elementType), new GoIntLiteral(0), null));
		GoForRangeBuilder forRangeBuilder = builder.forRange(pGoTLASetRefinement.getFrom().accept(this));

		GoVariableName v;
		if(pGoTLASetRefinement.getIdent().isTuple()) {
			v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
		}else {
			TLAIdentifier id = pGoTLASetRefinement.getIdent().getId();
			GoVariableName name = forRangeBuilder.initVariables(Arrays.asList("_", id.getId())).get(1);
			v = name;
			builder.linkUID(id.getUID(), name);
		}

		try (GoBlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
			if(pGoTLASetRefinement.getIdent().isTuple()) {
				List<TLAIdentifier> ids = pGoTLASetRefinement.getIdent().getTuple();
				for(int i = 0; i < ids.size(); ++i) {
					GoVariableName elem = forBody.varDecl(ids.get(i).getId(), new GoIndexExpression(v, new GoIntLiteral(i)));
					forBody.linkUID(ids.get(i).getUID(), elem);
				}
			}

			try (GoIfBuilder ifBuilder = forBody.ifStmt(pGoTLASetRefinement.getWhen().accept(
					new TLAExpressionCodeGenVisitor(forBody, registry, typeMap, globalStrategy)))) {
				try (GoBlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(tmpSet, new GoCall(new GoVariableName("append"), Arrays.asList(tmpSet, v)));
				}
			}
		}
		// no need to ensure uniqueness and sortedness, we're just removing elements
		return tmpSet;
	}

	@Override
	public GoExpression visit(TLAString pGoTLAString) throws RuntimeException {
		return new GoStringLiteral(pGoTLAString.getValue());
	}

	@Override
	public GoExpression visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLAUnary.getOperation().getUID()))
				.generateGo(
						builder, pGoTLAUnary, registry,
						Collections.singletonList(pGoTLAUnary.getOperand()),
						typeMap, globalStrategy);
	}

	@Override
	public GoExpression visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public GoExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return typeMap.get(plusCalDefaultInitValue.getUID()).accept(new PGoTypeGoTypeDefaultValueVisitor());
	}

	@Override
	public GoExpression visit(TLAFairness fairness) throws RuntimeException {
		throw new TODO();
	}
}
