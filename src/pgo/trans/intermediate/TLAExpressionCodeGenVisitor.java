package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

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

	private void unfoldQuantifierBounds(List<PGoTLAQuantifierBound> bounds, Consumer<BlockBuilder> action) {
		BlockBuilder currentBuilder = builder;
		List<BlockBuilder> accumulatedBuilders = new ArrayList<>();
		for (PGoTLAQuantifierBound bound : bounds) {
			if (bound.getIds().size() != 1) {
				throw new RuntimeException("TODO");
			}
			TLABuiltins.ensureSetType(typeMap, bound.getSet().getUID());
			Expression set = bound.getSet().accept(this);
			PGoTLAIdentifier id = bound.getIds().get(0);
			ForRangeBuilder forRangeBuilder = currentBuilder.forRange(set);
			VariableName name = forRangeBuilder.initVariables(Collections.singletonList(id.getId())).get(0);
			currentBuilder.linkUID(id.getUID(), name);
			currentBuilder = forRangeBuilder.getBlockBuilder();
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
		if (!(type instanceof PGoTypeSlice)) {
			throw new RuntimeException("TODO");
		}

		if (pGoTLAFunctionCall.getParams().size() != 1) {
			throw new RuntimeException("TODO");
		}
		return new Index(pGoTLAFunctionCall.getFunction().accept(this), pGoTLAFunctionCall.getParams().get(0).accept(this));
	}

	@Override
	public Expression visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		UID ref = registry.followReference(pGoTLABinOp.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.generateGo(
				builder, pGoTLABinOp, registry,
				Arrays.asList(
						pGoTLABinOp.getLHS().accept(this),
						pGoTLABinOp.getRHS().accept(this)),
				typeMap,
				globalStrategy);
	}

	@Override
	public Expression visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return pGoTLABool.getValue() ? Builtins.True : Builtins.False;
	}

	@Override
	public Expression visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLALet pGoTLALet) throws RuntimeException {
		throw new RuntimeException("TODO");
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
		// TODO: make this general
		Type elementType = new InterfaceType(Collections.emptyList());
		List<Expression> elements = new ArrayList<>();
		for (PGoTLAExpression element : pGoTLATuple.getElements()) {
			elements.add(element.accept(this));
		}
		return new SliceLiteral(elementType, elements);
	}

	@Override
	public Expression visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new RuntimeException("TODO");
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
						pGoTLAOperatorCall.getArgs().stream().map(a -> a.accept(this)).collect(Collectors.toList()),
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
					yes.addStatement(new GoTo(labelName));
				}
			}
		});
		builder.label(labelName);
		return exists;
	}

	@Override
	public Expression visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		Type elementType = TLABuiltins.ensureSetType(typeMap, pGoTLASetConstructor.getUID());
		VariableName tmpSet = builder.varDecl(
				"tmpSet",
				new SliceLiteral(
						elementType,
						pGoTLASetConstructor.getContents().stream()
								.map(e -> e.accept(this))
								.collect(Collectors.toList())));
		TLABuiltins.ensureUniqueSorted(builder, elementType, tmpSet);
		return tmpSet;
	}

	@Override
	public Expression visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		Type elementType = TLABuiltins.ensureSetType(typeMap, pGoTLASetComprehension.getUID());
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
		Type elementType = TLABuiltins.ensureSetType(typeMap, pGoTLASetRefinement.getUID());
		if (pGoTLASetRefinement.getIdent().isTuple()) {
			throw new RuntimeException("TODO");
		}
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
		VariableName v = forRangeBuilder.initVariables(Arrays.asList("_", "v")).get(1);
		builder.linkUID(pGoTLASetRefinement.getIdent().getId().getUID(), v);
		try (BlockBuilder forBody = forRangeBuilder.getBlockBuilder()) {
			try (IfBuilder ifBuilder = forBody.ifStmt(pGoTLASetRefinement.getWhen().accept(this))) {
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
						Collections.singletonList(pGoTLAUnary.getOperand().accept(this)),
						typeMap, globalStrategy);
	}

	@Override
	public Expression visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
