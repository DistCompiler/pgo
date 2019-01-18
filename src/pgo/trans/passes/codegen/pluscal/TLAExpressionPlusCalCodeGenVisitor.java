package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalMapping;
import pgo.model.pcal.*;
import pgo.scope.UID;
import pgo.model.tla.*;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

public class TLAExpressionPlusCalCodeGenVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAExpression> params;
	private final Map<UID, ModularPlusCalMapping> mappings;
	private final TemporaryBinding temporaryBinding;
	private final List<PlusCalStatement> output;

	public TLAExpressionPlusCalCodeGenVisitor(DefinitionRegistry registry,
	                                          Map<UID, PlusCalVariableDeclaration> arguments,
	                                          Map<UID, TLAExpression> params, Map<UID, ModularPlusCalMapping> mappings,
	                                          TemporaryBinding temporaryBinding, List<PlusCalStatement> output) {
		this.registry = registry;
		this.arguments = arguments;
		this.params = params;
		this.mappings = mappings;
		this.temporaryBinding = temporaryBinding;
		this.output = output;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : tlaFunctionCall.getParams()) {
			arguments.add(argument.accept(this));
		}
		return new TLAFunctionCall(tlaFunctionCall.getLocation(), tlaFunctionCall.getFunction(), arguments);
	}

	@Override
	public TLAExpression visit(TLABinOp tlaBinOp) throws RuntimeException {
		return new TLABinOp(
				tlaBinOp.getLocation(),
				tlaBinOp.getOperation(),
				tlaBinOp.getPrefix(),
				tlaBinOp.getLHS().accept(this),
				tlaBinOp.getRHS().accept(this));
	}

	@Override
	public TLAExpression visit(TLABool tlaBool) throws RuntimeException {
		return tlaBool.copy();
	}

	@Override
	public TLAExpression visit(TLACase tlaCase) throws RuntimeException {
		// translated as nested ifs
		TLAGeneralIdentifier caseResult = temporaryBinding.declare(tlaCase.getLocation(), new UID(), "caseResult");
		List<PlusCalStatement> currentBlock = output;
		for (TLACaseArm arm : tlaCase.getArms()) {
			TLAExpression condition = arm.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, arguments, params, mappings, temporaryBinding, currentBlock));
			List<PlusCalStatement> yes = new ArrayList<>();
			List<PlusCalStatement> no = new ArrayList<>();
			TLAExpression result = arm.getResult().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, arguments, params, mappings, temporaryBinding, yes));
			yes.add(new PlusCalAssignment(
					arm.getResult().getLocation(),
					Collections.singletonList(new PlusCalAssignmentPair(
							arm.getResult().getLocation(), caseResult, result))));
			currentBlock.add(new PlusCalIf(arm.getLocation(), condition, yes, no));
			currentBlock = no;
		}
		if (tlaCase.getOther() == null) {
			currentBlock.add(new PlusCalAssert(tlaCase.getLocation(), new TLABool(tlaCase.getLocation(), false)));
		} else {
			TLAExpression other = tlaCase.getOther().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, arguments, params, mappings, temporaryBinding, currentBlock));
			currentBlock.add(new PlusCalAssignment(
					tlaCase.getOther().getLocation(),
					Collections.singletonList(new PlusCalAssignmentPair(
							tlaCase.getOther().getLocation(), caseResult, other))));
		}
		return caseResult;
	}

	@Override
	public TLAExpression visit(TLAExistential tlaExistential) throws RuntimeException {
		return new TLAExistential(
				tlaExistential.getLocation(),
				tlaExistential.getIds(),
				tlaExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunction tlaFunction) throws RuntimeException {
		return new TLAFunction(
				tlaFunction.getLocation(), tlaFunction.getArguments(), tlaFunction.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		return new TLAFunctionSet(
				tlaFunctionSet.getLocation(),
				tlaFunctionSet.getFrom().accept(this),
				tlaFunctionSet.getTo().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		List<TLAFunctionSubstitutionPair> pairs = new ArrayList<>();
		for (TLAFunctionSubstitutionPair substitution : tlaFunctionSubstitution.getSubstitutions()) {
			List<TLASubstitutionKey> keys = new ArrayList<>();
			for (TLASubstitutionKey key : substitution.getKeys()) {
				List<TLAExpression> indices = new ArrayList<>();
				for (TLAExpression index : key.getIndices()) {
					indices.add(index.accept(this));
				}
				keys.add(new TLASubstitutionKey(key.getLocation(), indices));
			}
			pairs.add(new TLAFunctionSubstitutionPair(
					substitution.getLocation(),
					keys,
					substitution.getValue().accept(this)));
		}
		return new TLAFunctionSubstitution(
				tlaFunctionSubstitution.getLocation(),
				tlaFunctionSubstitution.getSource().accept(this),
				pairs);
	}

	@Override
	public TLAExpression visit(TLAIf tlaIf) throws RuntimeException {
		return new TLAIf(
				tlaIf.getLocation(),
				tlaIf.getCond().accept(this),
				tlaIf.getTval().accept(this),
				tlaIf.getFval().accept(this));
	}

	@Override
	public TLAExpression visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		SourceLocation location = tlaGeneralIdentifier.getLocation();
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (params.containsKey(varUID)) {
			TLAExpression value = params.get(varUID);
			UID valueUID = registry.followReference(value.getUID());
			TLAGeneralIdentifier variable = value instanceof TLARef
					? new TLAGeneralIdentifier(
							location,
							new TLAIdentifier(location, ((TLARef) value).getTarget()),
							Collections.emptyList())
					: (TLAGeneralIdentifier) value;
			boolean mappingsContainsValue = mappings.containsKey(valueUID);
			TLAGeneralIdentifier temp = temporaryBinding.declare(
					location,
					varUID,
					arguments.get(varUID).getName().getValue() + "Read");
			if (mappingsContainsValue) {
				ModularPlusCalMappingMacroExpansionVisitor visitor =
						new ModularPlusCalMappingMacroExpansionVisitor(
								temporaryBinding,
								temp,
								new TLAExpressionMappingMacroReadExpansionVisitor(
										registry, temporaryBinding, variable));
				for (PlusCalStatement statement : registry.findMappingMacro(mappings.get(valueUID).getTarget().getName()).getReadBody()) {
					output.addAll(statement.accept(visitor));
				}
			} else {
				TLAExpression rhs = value instanceof TLARef
						? new TLAGeneralIdentifier(
								location,
								new TLAIdentifier(location, ((TLARef) value).getTarget()),
								Collections.emptyList())
						: value;
				output.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, temp, rhs))));
			}
			return temp;
		}
		return temporaryBinding.lookup(varUID).orElse(tlaGeneralIdentifier);
	}

	@Override
	public TLAExpression visit(TLATuple tlaTuple) throws RuntimeException {
		List<TLAExpression> elements = new ArrayList<>();
		for (TLAExpression expression : tlaTuple.getElements()) {
			elements.add(expression.accept(this));
		}
		return new TLATuple(tlaTuple.getLocation(), elements);
	}

	@Override
	public TLAExpression visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		return new TLAMaybeAction(
				tlaMaybeAction.getLocation(),
				tlaMaybeAction.getBody().accept(this),
				tlaMaybeAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLANumber tlaNumber) throws RuntimeException {
		return tlaNumber.copy();
	}

	@Override
	public TLAExpression visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : tlaOperatorCall.getArgs()) {
			arguments.add(argument.accept(this));
		}
		return new TLAOperatorCall(
				tlaOperatorCall.getLocation(),
				tlaOperatorCall.getName(),
				tlaOperatorCall.getPrefix(),
				arguments);
	}

	private List<TLAQuantifierBound> transformBounds(List<TLAQuantifierBound> bounds) {
		List<TLAQuantifierBound> result = new ArrayList<>();
		for (TLAQuantifierBound bound : bounds) {
			result.add(new TLAQuantifierBound(
					bound.getLocation(),
					bound.getType(),
					bound.getIds(),
					bound.getSet().accept(this)));
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		return new TLAQuantifiedExistential(
				tlaQuantifiedExistential.getLocation(),
				transformBounds(tlaQuantifiedExistential.getIds()),
				tlaQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return new TLAQuantifiedUniversal(
				tlaQuantifiedUniversal.getLocation(),
				transformBounds(tlaQuantifiedUniversal.getIds()),
				tlaQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		List<TLARecordConstructor.Field> fields = new ArrayList<>();
		for (TLARecordConstructor.Field field : tlaRecordConstructor.getFields()) {
			fields.add(new TLARecordConstructor.Field(
					field.getLocation(), field.getName(), field.getValue().accept(this)));
		}
		return new TLARecordConstructor(tlaRecordConstructor.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		List<TLARecordSet.Field> fields = new ArrayList<>();
		for (TLARecordSet.Field field : tlaRecordSet.getFields()) {
			fields.add(new TLARecordSet.Field(field.getLocation(), field.getName(), field.getSet().accept(this)));
		}
		return new TLARecordSet(tlaRecordSet.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return new TLARequiredAction(
				tlaRequiredAction.getLocation(),
				tlaRequiredAction.getBody().accept(this),
				tlaRequiredAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		List<TLAExpression> contents = new ArrayList<>();
		for (TLAExpression expression : tlaSetConstructor.getContents()) {
			contents.add(expression.accept(this));
		}
		return new TLASetConstructor(tlaSetConstructor.getLocation(), contents);
	}

	@Override
	public TLAExpression visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		return new TLASetComprehension(
				tlaSetComprehension.getLocation(),
				tlaSetComprehension.getBody().accept(this),
				transformBounds(tlaSetComprehension.getBounds()));
	}

	@Override
	public TLAExpression visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		return new TLASetRefinement(
				tlaSetRefinement.getLocation(),
				tlaSetRefinement.getIdent(),
				tlaSetRefinement.getFrom().accept(this),
				tlaSetRefinement.getWhen().accept(this));
	}

	@Override
	public TLAExpression visit(TLAString tlaString) throws RuntimeException {
		return tlaString.copy();
	}

	@Override
	public TLAExpression visit(TLAUnary tlaUnary) throws RuntimeException {
		return new TLAUnary(
				tlaUnary.getLocation(),
				tlaUnary.getOperation(),
				tlaUnary.getPrefix(),
				tlaUnary.getOperand().accept(this));
	}

	@Override
	public TLAExpression visit(TLAUniversal tlaUniversal) throws RuntimeException {
		return new TLAUniversal(
				tlaUniversal.getLocation(),
				tlaUniversal.getIds(),
				tlaUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue.copy();
	}

	@Override
	public TLAExpression visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public TLAExpression visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
