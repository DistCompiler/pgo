package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.scope.UID;

public class TLAExpressionCodeGenVisitor extends PGoTLAExpressionVisitor<Expression, RuntimeException> {
	private BlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;
	private GlobalVariableStrategy globalStrategy;

	public TLAExpressionCodeGenVisitor(BlockBuilder builder, DefinitionRegistry registry, Map<UID, PGoType> typeMap, GlobalVariableStrategy globalStrategy) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
		this.globalStrategy = globalStrategy;
	}

	private List<Expression> evaluateQuantifierBoundSets(List<PGoTLAQuantifierBound> bounds){
		List<Expression> sets = new ArrayList<>();
		for(PGoTLAQuantifierBound qb : bounds){
			sets.add(qb.getSet().accept(this));
		}
		return sets;
	}

	private static Type getFunctionKeyType(Type fnType){
		Type keyValuePairType = ((SliceType)fnType).getElementType();
		return ((StructType)keyValuePairType).getFields().get(0).getType();
	}

	private void unfoldQuantifierBounds(List<PGoTLAQuantifierBound> bounds, Consumer<BlockBuilder> action){
		unfoldQuantifierBounds(bounds, evaluateQuantifierBoundSets(bounds), action);
	}

	private void unfoldQuantifierBounds(List<PGoTLAQuantifierBound> bounds, List<Expression> evaluatedSets, Consumer<BlockBuilder> action) {
		BlockBuilder currentBuilder = builder;
		List<BlockBuilder> accumulatedBuilders = new ArrayList<>();
		for (int i = 0; i < bounds.size(); ++i) {
			Expression set = evaluatedSets.get(i);
			PGoTLAQuantifierBound bound = bounds.get(i);
			ForRangeBuilder forRangeBuilder = currentBuilder.forRange(set);

			if (bound.getType() == PGoTLAQuantifierBound.Type.TUPLE) {
				VariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
				currentBuilder = forRangeBuilder.getBlockBuilder();

				// useful for some internal codegen, not needed by user code
				currentBuilder.linkUID(bound.getUID(), v);

				List<PGoTLAIdentifier> ids = bound.getIds();
				for(int j = 0; j < ids.size(); ++j) {
					VariableName name = currentBuilder.varDecl(ids.get(j).getId(), new Index(v, new IntLiteral(j)));
					currentBuilder.linkUID(ids.get(j).getUID(), name);
				}
			}else {
				if (bound.getIds().size() != 1) {
					throw new TODO();
				}

				PGoTLAIdentifier id = bound.getIds().get(0);
				VariableName name = forRangeBuilder.initVariables(Arrays.asList("_", id.getId())).get(1);
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
	public Expression visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		PGoType type = typeMap.get(pGoTLAFunctionCall.getFunction().getUID());
		if(type instanceof PGoTypeFunction){
			Expression function = pGoTLAFunctionCall.getFunction().accept(this);
			List<Expression> params = new ArrayList<>();
			for(PGoTLAExpression param : pGoTLAFunctionCall.getParams()){
				params.add(param.accept(this));
			}

			Type keyType = getFunctionKeyType(type.accept(new PGoTypeGoTypeConversionVisitor()));
			VariableName key;
			if(pGoTLAFunctionCall.getParams().size() == 1){
				key = builder.varDecl("key", params.get(0));
			}else{
				if(keyType instanceof SliceType){
					Type elementType = ((SliceType)keyType).getElementType();
					key = builder.varDecl("key", new SliceLiteral(elementType, params));
				}else if(keyType instanceof StructType){
					List<StructLiteralField> fields = new ArrayList<>();
					for(Expression param : params){
						fields.add(new StructLiteralField(null, param));
					}
					key = builder.varDecl("key", new StructLiteral(keyType, fields));
				}else {
					throw new InternalCompilerError();
				}
			}

			AnonymousFunctionBuilder comparatorBuilder = builder.anonymousFunction();
			VariableName i = comparatorBuilder.addArgument("i", Builtins.Int);
			comparatorBuilder.addReturn(Builtins.Bool);
			try(BlockBuilder comparatorBody = comparatorBuilder.getBlockBuilder()){
				comparatorBody.addStatement(
						new Return(Collections.singletonList(
								new Unary(
										Unary.Operation.NOT,
										keyType.accept(new LessThanCodeGenVisitor(
												comparatorBody,
												new Selector(new Index(function, i), "key"),
												key))))));
			}
			VariableName index = builder.varDecl("index", new Call(
					new Selector(new VariableName("sort"), "Search"),
					Arrays.asList(
							new Call(new VariableName("len"), Collections.singletonList(function)),
							comparatorBuilder.getFunction())));
			return new Selector(new Index(function, index), "value");
		}else if(type instanceof PGoTypeSlice){
			if (pGoTLAFunctionCall.getParams().size() != 1) {
				throw new InternalCompilerError(); // slices fundamentally cannot be indexed by multiple parameters
			}
			return new Index(
					pGoTLAFunctionCall.getFunction().accept(this),
					new Binop(
							Binop.Operation.MINUS,
							pGoTLAFunctionCall.getParams().get(0).accept(this),
							new IntLiteral(1)));
		}else{
			throw new InternalCompilerError();
		}
	}

	@Override
	public Expression visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		UID ref = registry.followReference(pGoTLABinOp.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.generateGo(
				builder, pGoTLABinOp, registry,
				Arrays.asList(
						pGoTLABinOp.getLHS(),
						pGoTLABinOp.getRHS()),
				typeMap,
				globalStrategy);
	}

	@Override
	public Expression visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return pGoTLABool.getValue() ? Builtins.True : Builtins.False;
	}

	@Override
	public Expression visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		Type mapType = typeMap.get(pGoTLAFunction.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		Expression capacity = null;
		List<PGoTLAQuantifierBound> args = pGoTLAFunction.getArguments();
		List<Expression> domains = evaluateQuantifierBoundSets(args);
		for(int argPos = 0; argPos < args.size(); ++argPos){
			Expression domain = domains.get(argPos);
			Expression currentTerm = new Call(new VariableName("len"), Collections.singletonList(domain));
			if(capacity == null){
				capacity = currentTerm;
			}else{
				capacity = new Binop(Binop.Operation.TIMES, capacity, currentTerm);
			}
		}
		VariableName function = builder.varDecl("function", new Make(mapType, new IntLiteral(0), capacity));
		unfoldQuantifierBounds(pGoTLAFunction.getArguments(), domains, innerBuilder -> {
			Type keyValuePairType = ((SliceType)mapType).getElementType();
			Expression key;
			if(args.size() == 1){
				key = innerBuilder.findUID(args.get(0).getUID());
			}else{
				Type keyType = ((StructType)keyValuePairType).getFields().get(0).getType();
				List<StructLiteralField> keyFields = new ArrayList<>();
				for(PGoTLAQuantifierBound qb : args){
					keyFields.add(new StructLiteralField(null, innerBuilder.findUID(qb.getUID())));
				}
				key = new StructLiteral(keyType, keyFields);
			}
			Expression value = pGoTLAFunction.getBody().accept(
					new TLAExpressionCodeGenVisitor(innerBuilder, registry, typeMap, globalStrategy));
			Expression keyValuePair = new StructLiteral(keyValuePairType, Arrays.asList(
					new StructLiteralField("key", key),
					new StructLiteralField("value", value)
			));
			innerBuilder.assign(function, new Call(new VariableName("append"), Arrays.asList(function, keyValuePair)));
		});
		return function;
	}

	@Override
	public Expression visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
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
	public Expression visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		Type sliceType = typeMap.get(pGoTLATuple.getUID()).accept(new PGoTypeGoTypeConversionVisitor());
		List<Expression> elements = new ArrayList<>();
		for (PGoTLAExpression element : pGoTLATuple.getElements()) {
			elements.add(element.accept(this));
		}
		return sliceType.accept(new TLATupleCodeGenVisitor(builder, elements));
	}

	@Override
	public Expression visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		return new IntLiteral(Integer.valueOf(pGoTLANumber.getVal()));
	}

	@Override
	public Expression visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLAOperatorCall.getName().getUID()))
				.generateGo(
						builder, pGoTLAOperatorCall, registry,
						pGoTLAOperatorCall.getArgs(),
						typeMap, globalStrategy);
	}

	@Override
	public Expression visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		LabelName labelName = builder.newLabel("yes");
		VariableName exists = builder.varDecl("exists", Builtins.False);
		unfoldQuantifierBounds(pGoTLAQuantifiedExistential.getIds(), innerBlock -> {
			// needs a new visitor because we must write to the inner block rather than the outer block
			try (IfBuilder ifBuilder = innerBlock.ifStmt(pGoTLAQuantifiedExistential.getBody()
					.accept(new TLAExpressionCodeGenVisitor(innerBlock, registry, typeMap, globalStrategy)))) {
				try (BlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(exists, Builtins.True);
					if(pGoTLAQuantifiedExistential.getIds().size() == 1) {
						yes.addStatement(new Break());
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
	public Expression visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		Type elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetConstructor.getUID()));
		Expression result = new SliceLiteral(
				elementType,
				pGoTLASetConstructor.getContents().stream()
						.map(e -> e.accept(this))
						.collect(Collectors.toList()));
		if(pGoTLASetConstructor.getContents().size() <= 1) {
			// single-element or empty sets don't need any sorting or deduplication
			return result;
		}else {
			VariableName tmpSet = builder.varDecl("tmpSet", result);
			TLABuiltins.ensureUniqueSorted(builder, elementType, tmpSet);
			return tmpSet;
		}
	}

	@Override
	public Expression visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		Type elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetComprehension.getUID()));
		VariableName accumulator = builder.varDecl(
				"tmpSet", new Make(new SliceType(elementType), new IntLiteral(0), null));
		unfoldQuantifierBounds(pGoTLASetComprehension.getBounds(), innerBuilder -> {
			Expression body = pGoTLASetComprehension.getBody().accept(new TLAExpressionCodeGenVisitor(
					innerBuilder, registry, typeMap, globalStrategy));
			innerBuilder.assign(accumulator, new Call(new VariableName("append"), Arrays.asList(accumulator, body)));
		});
		TLABuiltins.ensureUniqueSorted(builder, elementType, accumulator);
		return accumulator;
	}

	@Override
	public Expression visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		Type elementType = TLABuiltins.getSetElementType(typeMap.get(pGoTLASetRefinement.getUID()));
		// Go code
		// tmpSet := make([]Type, 0)
		// for _, v := range pGoTLASetRefinement.getFrom() {
		// 	if pGoTLASetRefinement.getWhen() {
		// 		tmpSet = append(tmpSet, v)
		// 	}
		// }
		VariableName tmpSet = builder.varDecl(
				"tmpSet", new Make(new SliceType(elementType), new IntLiteral(0), null));
		ForRangeBuilder forRangeBuilder = builder.forRange(pGoTLASetRefinement.getFrom().accept(this));

		VariableName v;
		if(pGoTLASetRefinement.getIdent().isTuple()) {
			v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
		}else {
			PGoTLAIdentifier id = pGoTLASetRefinement.getIdent().getId();
			VariableName name = forRangeBuilder.initVariables(Arrays.asList("_", id.getId())).get(1);
			v = name;
			builder.linkUID(id.getUID(), name);
		}

		try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
			if(pGoTLASetRefinement.getIdent().isTuple()) {
				List<PGoTLAIdentifier> ids = pGoTLASetRefinement.getIdent().getTuple();
				for(int i = 0; i < ids.size(); ++i) {
					VariableName elem = forBody.varDecl(ids.get(i).getId(), new Index(v, new IntLiteral(i)));
					forBody.linkUID(ids.get(i).getUID(), elem);
				}
			}

			try (IfBuilder ifBuilder = forBody.ifStmt(pGoTLASetRefinement.getWhen().accept(
					new TLAExpressionCodeGenVisitor(forBody, registry, typeMap, globalStrategy)))) {
				try (BlockBuilder yes = ifBuilder.whenTrue()) {
					yes.assign(tmpSet, new Call(new VariableName("append"), Arrays.asList(tmpSet, v)));
				}
			}
		}
		// no need to ensure uniqueness and sortedness, we're just removing elements
		return tmpSet;
	}

	@Override
	public Expression visit(PGoTLAString pGoTLAString) throws RuntimeException {
		return new StringLiteral(pGoTLAString.getValue());
	}

	@Override
	public Expression visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLAUnary.getOperation().getUID()))
				.generateGo(
						builder, pGoTLAUnary, registry,
						Collections.singletonList(pGoTLAUnary.getOperand()),
						typeMap, globalStrategy);
	}

	@Override
	public Expression visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Expression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return typeMap.get(plusCalDefaultInitValue.getUID()).accept(new PGoTypeGoTypeDefaultValueVisitor());
	}
}
