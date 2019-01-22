package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;

public class ModularPlusCalCodeGenVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final DefinitionRegistry registry;
	private final TemporaryBinding readTemporaryBinding;
	private final TemporaryBinding writeTemporaryBinding;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAGeneralIdentifier> params;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Set<UID> refs;
	private final Set<UID> functionMappedVars;
	private final Map<UID, Set<UID>> labelsToVarReads;
	private final Map<UID, Set<UID>> labelsToVarWrites;

	ModularPlusCalCodeGenVisitor(DefinitionRegistry registry, Map<UID, Set<UID>> labelsToVarReads,
	                             Map<UID, Set<UID>> labelsToVarWrites, Map<UID, PlusCalVariableDeclaration> arguments,
	                             Map<UID, TLAGeneralIdentifier> params, Map<UID, ModularPlusCalMappingMacro> mappings,
	                             Set<UID> refs, Set<UID> functionMappedVars, TemporaryBinding readTemporaryBinding,
	                             TemporaryBinding writeTemporaryBinding) {
		this.registry = registry;
		this.labelsToVarReads = labelsToVarReads;
		this.labelsToVarWrites = labelsToVarWrites;
		this.arguments = arguments;
		this.params = params;
		this.mappings = mappings;
		this.refs = refs;
		this.functionMappedVars = functionMappedVars;
		this.readTemporaryBinding = readTemporaryBinding;
		this.writeTemporaryBinding = writeTemporaryBinding;
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		UID labelUID = plusCalLabeledStatements.getLabel().getUID();
		SourceLocation labelLocation = plusCalLabeledStatements.getLabel().getLocation();
		// translate the statements in this labeledStatements
		List<PlusCalStatement> statements = new ArrayList<>(substituteStatements(plusCalLabeledStatements.getStatements()));
		// write back the written values and clean up
		Set<UID> touchedVariables = new LinkedHashSet<>();
		if (labelsToVarReads.containsKey(labelUID)) {
			touchedVariables.addAll(labelsToVarReads.get(labelUID));
		}
		if (labelsToVarWrites.containsKey(labelUID)) {
			touchedVariables.addAll(labelsToVarWrites.get(labelUID));
		}
		for (UID varUID : touchedVariables) {
			// only write back written refs
			TLAGeneralIdentifier variable = params.get(varUID);
			if (writeTemporaryBinding.lookup(varUID).isPresent() && refs.contains(varUID)) {
				TLAGeneralIdentifier rhs = writeTemporaryBinding.lookup(varUID).get();
				statements.add(new PlusCalAssignment(
						labelLocation,
						Collections.singletonList(new PlusCalAssignmentPair(labelLocation, variable, rhs))));
			}
			// clean up
			readTemporaryBinding.reuse(varUID);
			writeTemporaryBinding.reuse(varUID);
		}
		return Collections.singletonList(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(),
				statements));
	}

	private <T> void reuseWrites(Map<UID, T> touchedVars) {
		for (UID varUID : touchedVars.keySet()) {
			writeTemporaryBinding.reuse(varUID);
		}
	}

	private <T> void declareJoinNames(SourceLocation location, Map<UID, T> varUIDs,
	                              Map<UID, TLAGeneralIdentifier> output) {
		for (UID varUID : varUIDs.keySet()) {
			if (params.containsKey(varUID) && !output.containsKey(varUID)) {
				output.put(
						varUID,
						writeTemporaryBinding.forceDeclare(
								location, varUID, arguments.get(varUID).getName().getValue() + "Write"));
			}
		}
	}

	private void writeJoinAssignments(SourceLocation location, Map<UID, TLAGeneralIdentifier> touchedVars,
	                                  Map<UID, TLAGeneralIdentifier> writes, List<PlusCalStatement> output) {
		for (Map.Entry<UID, TLAGeneralIdentifier> entry : touchedVars.entrySet()) {
			UID varUID = entry.getKey();
			TLAGeneralIdentifier writeVar = entry.getValue();
			if (writes.containsKey(varUID)) {
				output.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, writeVar, writes.get(varUID)))));
			} else {
				output.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(
								location, writeVar, params.get(varUID)))));
			}
		}
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		// all while loops are already desugared into ifs and gotos in the previous desugaring phase
        throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		SourceLocation location = plusCalIf.getLocation();

		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalIf.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result));

		writeTemporaryBinding.startRecording();
		List<PlusCalStatement> yes = substituteStatements(plusCalIf.getYes());
		Map<UID, TLAGeneralIdentifier> yesWrites = writeTemporaryBinding.stopRecording();

		writeTemporaryBinding.startRecording();
		List<PlusCalStatement> no = substituteStatements(plusCalIf.getNo());
		Map<UID, TLAGeneralIdentifier> noWrites = writeTemporaryBinding.stopRecording();
		reuseWrites(noWrites);

		Map<UID, TLAGeneralIdentifier> touchedVars = new LinkedHashMap<>();
		declareJoinNames(location, yesWrites, touchedVars);
		declareJoinNames(location, noWrites, touchedVars);
		writeJoinAssignments(location, touchedVars, yesWrites, yes);
		writeJoinAssignments(location, touchedVars, noWrites, no);

		result.add(new PlusCalIf(location, condition, yes, no));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		SourceLocation location = plusCalEither.getLocation();
		List<List<PlusCalStatement>> transformedCases = new ArrayList<>();
		List<Map<UID, TLAGeneralIdentifier>> writesList = new ArrayList<>();
		List<List<PlusCalStatement>> cases = plusCalEither.getCases();
		for (List<PlusCalStatement> aCase : cases) {
			writeTemporaryBinding.startRecording();
			transformedCases.add(substituteStatements(aCase));
			Map<UID, TLAGeneralIdentifier> touchedVars = writeTemporaryBinding.stopRecording();
			reuseWrites(touchedVars);
			writesList.add(touchedVars);
		}
		Map<UID, TLAGeneralIdentifier> touchedVars = new LinkedHashMap<>();
		for (Map<UID, TLAGeneralIdentifier> uids : writesList) {
			declareJoinNames(location, uids, touchedVars);
		}
		for (int i = 0; i < transformedCases.size(); i++) {
			List<PlusCalStatement> transformedCase = transformedCases.get(i);
			Map<UID, TLAGeneralIdentifier> writes = writesList.get(i);
			writeJoinAssignments(location, touchedVars, writes, transformedCase);
		}
		return Collections.singletonList(new PlusCalEither(location, transformedCases));
	}

	private void assignmentHelper(SourceLocation location, TLAExpression lhs, TLAExpression rhs,
	                              List<PlusCalStatement> result) {
		TLAExpression transformedLHS = lhs.accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result));
		result.add(new PlusCalAssignment(
				location,
				Collections.singletonList(new PlusCalAssignmentPair(location, transformedLHS, rhs))));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<PlusCalAssignmentPair> pairs = plusCalAssignment.getPairs();
		List<TLAExpression> rhsList = new ArrayList<>();
		if (pairs.size() > 1) {
			TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
					registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding,
					writeTemporaryBinding, result);
			// read the RHS into temporary variables for use later so that parallel assignment works right
			for (PlusCalAssignmentPair pair : pairs) {
				SourceLocation location = pair.getLocation();
				TLAExpression rhs = pair.getRhs();
				TLAGeneralIdentifier tempVariable = readTemporaryBinding.declare(location, new UID(), "rhsRead");
				TLAExpression transformedRHS = rhs.accept(visitor);
				result.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, tempVariable, transformedRHS))));
				rhsList.add(tempVariable);
			}
		} else {
			// otherwise, don't create temporary variable for cleaner code
			rhsList.add(pairs.get(0).getRhs().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding,
					writeTemporaryBinding, result)));
		}
		for (int i = 0; i < pairs.size(); i++) {
			PlusCalAssignmentPair pair = pairs.get(i);
			SourceLocation location = pair.getLocation();
			TLAExpression lhs = pair.getLhs();
			TLAExpression rhs = rhsList.get(i);
			TLAGeneralIdentifier identifier = null;
			List<TLAExpression> accumulatedIndices = new ArrayList<>();
			if (lhs instanceof TLAFunctionCall) {
				Optional<TLAGeneralIdentifier> optionalVariable =
						TLAExpressionPlusCalCodeGenVisitor.extractFunctionCallIdentifier(
								(TLAFunctionCall) lhs, accumulatedIndices);
				if (optionalVariable.isPresent()) {
					identifier = optionalVariable.get();
				}
			} else if (lhs instanceof TLAGeneralIdentifier) {
				identifier = (TLAGeneralIdentifier) lhs;
			}
			if (identifier == null) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			UID varUID = registry.followReference(identifier.getUID());
			if (!mappings.containsKey(varUID)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			TLAGeneralIdentifier dollarVariable = params.get(varUID);
			PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> writeVisitor;
			if (lhs instanceof TLAFunctionCall) {
				TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
						registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding,
						writeTemporaryBinding, result);
				for (int j = accumulatedIndices.size() - 1; j >= 0; j--) {
					accumulatedIndices.set(j, accumulatedIndices.get(j).accept(visitor));
				}
				TLAExpression index = functionMappedVars.contains(varUID) ? accumulatedIndices.get(0) : null;
				writeVisitor = new ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor(
						readTemporaryBinding,
						writeTemporaryBinding,
						dollarVariable,
						varUID,
						arguments.get(varUID).getName().getValue() + "Write",
						index,
						accumulatedIndices, new TLAExpressionMappingMacroWriteExpansionVisitor(
								registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, rhs, varUID,
								index));
			} else {
				writeVisitor = new ModularPlusCalMappingMacroVariableWriteExpansionVisitor(
						readTemporaryBinding,
						writeTemporaryBinding,
						dollarVariable,
						varUID,
						arguments.get(varUID).getName().getValue() + "Write",
						null, new TLAExpressionMappingMacroWriteExpansionVisitor(
								registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, rhs, varUID,
								null));
			}
			for (PlusCalStatement statement : mappings.get(varUID).getWriteBody()) {
				result.addAll(statement.accept(writeVisitor));
			}
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return Collections.singletonList(new PlusCalReturn(plusCalReturn.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(plusCalSkip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<TLAExpression> args = new ArrayList<>();
		TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result);
		for (TLAExpression argument : plusCalCall.getArguments()) {
			args.add(argument.accept(visitor));
		}
		result.add(new PlusCalCall(plusCalCall.getLocation(), plusCalCall.getTarget(), args));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<PlusCalVariableDeclaration> declarations = new ArrayList<>();
		TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result);
		for (PlusCalVariableDeclaration declaration : plusCalWith.getVariables()) {
			declarations.add(new PlusCalVariableDeclaration(
					declaration.getLocation(),
					declaration.getName(),
					false,
					declaration.isSet(),
					declaration.getValue().accept(visitor)));
		}
		result.add(new PlusCalWith(
				plusCalWith.getLocation(), declarations, substituteStatements(plusCalWith.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalPrint.getValue().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result));
		result.add(new PlusCalPrint(plusCalPrint.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalAssert.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result));
		result.add(new PlusCalAssert(plusCalAssert.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalAwait.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, arguments, params, mappings, functionMappedVars, readTemporaryBinding, writeTemporaryBinding,
				result));
		result.add(new PlusCalAwait(plusCalAwait.getLocation(), condition));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(plusCalGoto.copy());
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
