package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;

public class TLAExpressionPlusCalCodeGenVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final Map<UID, PlusCalVariableDeclaration> params;
	private final Map<UID, TLAGeneralIdentifier> arguments;
	private final Set<UID> expressionArguments;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Set<UID> functionMappedVars;
	private final TemporaryBinding readTemporaryBinding;
	private final TemporaryBinding writeTemporaryBinding;
	private final ProcedureExpander procedureExpander;
	private final List<PlusCalStatement> output;

	TLAExpressionPlusCalCodeGenVisitor(DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
	                                   Map<UID, TLAGeneralIdentifier> arguments, Set<UID> expressionArguments,
	                                   Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> functionMappedVars,
	                                   TemporaryBinding readTemporaryBinding, TemporaryBinding writeTemporaryBinding,
	                                   ProcedureExpander procedureExpander, List<PlusCalStatement> output) {
		this.registry = registry;
		this.params = params;
		this.arguments = arguments;
		this.expressionArguments = expressionArguments;
		this.mappings = mappings;
		this.functionMappedVars = functionMappedVars;
		this.readTemporaryBinding = readTemporaryBinding;
		this.writeTemporaryBinding = writeTemporaryBinding;
		this.procedureExpander = procedureExpander;
		this.output = output;
	}

	static Optional<TLAGeneralIdentifier> extractFunctionCallIdentifier(TLAFunctionCall fnCall,
	                                                                    List<TLAExpression> accumulatedIndices) {
		SourceLocation location = fnCall.getLocation();
		TLAExpression fn = fnCall.getFunction();
		List<TLAExpression> fnParams = fnCall.getParams();
		if (fnParams.size() > 1) {
			accumulatedIndices.add(new TLATuple(location, fnParams));
		} else if (fnParams.size() == 1) {
			accumulatedIndices.add(fnParams.get(0));
		} else {
			accumulatedIndices.add(new TLATuple(location, Collections.emptyList()));
		}
		if (fn instanceof TLAGeneralIdentifier) {
			int size = accumulatedIndices.size();
			for (int i = 0; i < size; i++) {
				TLAExpression temp = accumulatedIndices.set(i, accumulatedIndices.get(size - i - 1));
				accumulatedIndices.set(size - i - 1, temp);
			}
			return Optional.of((TLAGeneralIdentifier) fn);
		}
		if (fn instanceof TLAFunctionCall) {
			return extractFunctionCallIdentifier((TLAFunctionCall) fn, accumulatedIndices);
		}
		accumulatedIndices.clear();
		return Optional.empty();
	}

	private void substituteReadBody(TLAGeneralIdentifier temp, TLAGeneralIdentifier dollarVariable, UID varUID,
	                                TLAExpression index) {
		ModularPlusCalMappingMacroReadExpansionVisitor visitor =
				new ModularPlusCalMappingMacroReadExpansionVisitor(
						registry,
						params,
						arguments,
						mappings,
						expressionArguments,
						functionMappedVars,
						readTemporaryBinding,
						writeTemporaryBinding,
						procedureExpander,
						dollarVariable,
						varUID,
						params.get(varUID).getName().getValue() + "Write",
						index,
						new TLAExpressionMappingMacroReadExpansionVisitor(
								registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, varUID, index),
						temp);
		for (PlusCalStatement statement : mappings.get(varUID).getReadBody()) {
			output.addAll(statement.accept(visitor));
		}
	}

	@Override
	public TLAExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		List<TLAExpression> accumulatedIndices = new ArrayList<>();
		Optional<TLAGeneralIdentifier> optionalVariable = extractFunctionCallIdentifier(
				tlaFunctionCall, accumulatedIndices);
		if (optionalVariable.isPresent()) {
			TLAGeneralIdentifier variable = optionalVariable.get();
			UID varUID = registry.followReference(variable.getUID());
			if (functionMappedVars.contains(varUID)) {
				for (int j = accumulatedIndices.size() - 1; j >= 0; j--) {
					accumulatedIndices.set(j, accumulatedIndices.get(j).accept(this));
				}
				TLAExpression index = accumulatedIndices.get(0);
				accumulatedIndices = accumulatedIndices.subList(1, accumulatedIndices.size());
				TLAGeneralIdentifier temp = readTemporaryBinding.declare(
						variable.getLocation(),
						varUID,
						params.get(varUID).getName().getValue() + "Read");
				substituteReadBody(temp, arguments.get(varUID), varUID, index);
				if (accumulatedIndices.size() > 0) {
					return new TLAFunctionCall(tlaFunctionCall.getLocation(), temp, accumulatedIndices);
				}
				return temp;
			}
		}
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : tlaFunctionCall.getParams()) {
			arguments.add(argument.accept(this));
		}
		return new TLAFunctionCall(
				tlaFunctionCall.getLocation(), tlaFunctionCall.getFunction().accept(this), arguments);
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
		TLAGeneralIdentifier caseResult = readTemporaryBinding.declare(tlaCase.getLocation(), new UID(), "caseResult");
		List<PlusCalStatement> currentBlock = output;
		for (TLACaseArm arm : tlaCase.getArms()) {
			TLAExpression condition = arm.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, params, arguments, expressionArguments, mappings, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander, currentBlock));
			List<PlusCalStatement> yes = new ArrayList<>();
			List<PlusCalStatement> no = new ArrayList<>();
			TLAExpression result = arm.getResult().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, params, arguments, expressionArguments, mappings, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander, yes));
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
					registry, params, arguments, expressionArguments, mappings, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander, currentBlock));
			currentBlock.add(new PlusCalAssignment(
					tlaCase.getOther().getLocation(),
					Collections.singletonList(new PlusCalAssignmentPair(
							tlaCase.getOther().getLocation(), caseResult, other))));
		}
		return caseResult;
	}

	@Override
	public TLAExpression visit(TLADot tlaDot) throws RuntimeException {
		return new TLADot(tlaDot.getLocation(), tlaDot.getExpression().accept(this), tlaDot.getField());
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
		TLAGeneralIdentifier ifResult = readTemporaryBinding.declare(tlaIf.getLocation(), new UID(), "ifResult");
		TLAExpression condition = tlaIf.getCond().accept(this);
		List<PlusCalStatement> yes = new ArrayList<>();
		TLAExpression yesResult = tlaIf.getTval().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, yes));
		yes.add(new PlusCalAssignment(
				tlaIf.getTval().getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						tlaIf.getTval().getLocation(), ifResult, yesResult))));
		List<PlusCalStatement> no = new ArrayList<>();
		TLAExpression noResult = tlaIf.getFval().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, no));
		no.add(new PlusCalAssignment(
				tlaIf.getFval().getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						tlaIf.getFval().getLocation(), ifResult, noResult))));
		output.add(new PlusCalIf(tlaIf.getLocation(), condition, yes, no));
		return ifResult;
	}

	@Override
	public TLAExpression visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		SourceLocation location = tlaGeneralIdentifier.getLocation();
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (arguments.containsKey(varUID)) {
			TLAGeneralIdentifier dollarVariable = arguments.get(varUID);
			TLAGeneralIdentifier temp = readTemporaryBinding.declare(
					location,
					varUID,
					params.get(varUID).getName().getValue() + "Read");
			if (mappings.containsKey(varUID)) {
				substituteReadBody(temp, dollarVariable, varUID, null);
			} else {
				output.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(
								location, temp, writeTemporaryBinding.lookup(varUID).orElse(dollarVariable)))));
			}
			return temp;
		}
		return readTemporaryBinding.lookup(varUID).orElse(tlaGeneralIdentifier);
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
