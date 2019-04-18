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

public class ModularPlusCalCodeGenVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final DefinitionRegistry registry;
	protected final TemporaryBinding readTemporaryBinding;
	protected final TemporaryBinding writeTemporaryBinding;
	private final Map<UID, PlusCalVariableDeclaration> params;
	private final Map<UID, TLAGeneralIdentifier> arguments;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Set<UID> expressionArguments;
	private final Set<UID> functionMappedVars;
	private final ProcedureExpander procedureExpander;

	ModularPlusCalCodeGenVisitor(DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
	                             Map<UID, TLAGeneralIdentifier> arguments,
	                             Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> expressionArguments,
	                             Set<UID> functionMappedVars, TemporaryBinding readTemporaryBinding,
	                             TemporaryBinding writeTemporaryBinding, ProcedureExpander procedureExpander) {
		this.registry = registry;
		this.params = params;
		this.arguments = arguments;
		this.mappings = mappings;
		this.expressionArguments = expressionArguments;
		this.functionMappedVars = functionMappedVars;
		this.readTemporaryBinding = readTemporaryBinding;
		this.writeTemporaryBinding = writeTemporaryBinding;
		this.procedureExpander = procedureExpander;
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	private List<PlusCalStatement> substituteBlock(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (int i = 0; i < statements.size(); i++) {
			PlusCalStatement statement = statements.get(i);
			if (statement instanceof PlusCalLabeledStatements) {
				List<PlusCalStatement> writeBacks = getWriteBacksAndCleanUp(statement.getLocation());
				if (writeBacks.size() > 0) {
					result = WriteBackInsertionVisitor.insertWriteBacks(result, writeBacks);
				}
				result.addAll(substituteStatements(statements.subList(i, statements.size())));
				return result;
			}
			result.addAll(statement.accept(this));
		}
		return result;
	}


	private List<PlusCalStatement> getWriteBacksAndCleanUp(SourceLocation location) {
		List<PlusCalStatement> writeBacks = new ArrayList<>();
		for (UID varUID : arguments.keySet()) {
			// only write back written global variables
			TLAGeneralIdentifier variable = arguments.get(varUID);
			if (writeTemporaryBinding.lookup(varUID).isPresent()) {
				TLAGeneralIdentifier rhs = writeTemporaryBinding.lookup(varUID).get();
				writeBacks.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, variable, rhs))));
			}
		}
		// clean up
		readTemporaryBinding.reuseAll();
		writeTemporaryBinding.reuseAll();
		return writeBacks;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		for (UID varUID : expressionArguments) {
			readTemporaryBinding.declare(
					plusCalLabeledStatements.getLocation(), varUID, params.get(varUID).getName().getValue() + "Local");
		}
		// translate the statements in this labeledStatements
		List<PlusCalStatement> statements = substituteStatements(plusCalLabeledStatements.getStatements());
		// write back the written values and clean up
		List<PlusCalStatement> writeBacks = getWriteBacksAndCleanUp(plusCalLabeledStatements.getLabel().getLocation());
		return Collections.singletonList(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(),
				writeBacks.size() > 0
						? WriteBackInsertionVisitor.insertWriteBacks(statements, writeBacks)
						: statements));
	}

	private <T> void declareJoinNames(SourceLocation location, Map<UID, T> varUIDs,
	                                  Map<UID, TLAGeneralIdentifier> output) {
		for (UID varUID : varUIDs.keySet()) {
			if (arguments.containsKey(varUID) && !output.containsKey(varUID)) {
				output.put(
						varUID,
						writeTemporaryBinding.forceDeclare(
								location, varUID, params.get(varUID).getName().getValue() + "Write"));
			}
		}
	}

	private List<PlusCalStatement> writeJoinAssignments(SourceLocation location,
	                                                    Map<UID, TLAGeneralIdentifier> touchedVars,
	                                                    Map<UID, TLAGeneralIdentifier> writes,
	                                                    List<PlusCalStatement> output) {
		List<PlusCalStatement> joinAssignments = new ArrayList<>();
		for (Map.Entry<UID, TLAGeneralIdentifier> entry : touchedVars.entrySet()) {
			UID varUID = entry.getKey();
			TLAGeneralIdentifier writeVar = entry.getValue();
			if (writes.containsKey(varUID)) {
				joinAssignments.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, writeVar, writes.get(varUID)))));
			} else {
				joinAssignments.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(
								location, writeVar, arguments.get(varUID)))));
			}
		}
		return WriteBackInsertionVisitor.insertWriteBacks(output, joinAssignments);
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
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result));

		TemporaryBinding.Checkpoint checkpoint = writeTemporaryBinding.checkpoint();
		Map<UID, TLAGeneralIdentifier> yesWrites = writeTemporaryBinding.startRecording();
		List<PlusCalStatement> yes = substituteBlock(plusCalIf.getYes());
		writeTemporaryBinding.stopRecording();
		writeTemporaryBinding.restore(checkpoint);

		Map<UID, TLAGeneralIdentifier> noWrites = writeTemporaryBinding.startRecording();
		List<PlusCalStatement> no = substituteBlock(plusCalIf.getNo());
		writeTemporaryBinding.stopRecording();

		Map<UID, TLAGeneralIdentifier> touchedVars = new LinkedHashMap<>();
		declareJoinNames(location, yesWrites, touchedVars);
		declareJoinNames(location, noWrites, touchedVars);

		result.add(new PlusCalIf(
				location,
				condition,
				writeJoinAssignments(location, touchedVars, yesWrites, yes),
				writeJoinAssignments(location, touchedVars, noWrites, no)));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		SourceLocation location = plusCalEither.getLocation();
		List<List<PlusCalStatement>> transformedCases = new ArrayList<>();
		List<Map<UID, TLAGeneralIdentifier>> writesList = new ArrayList<>();
		List<List<PlusCalStatement>> cases = plusCalEither.getCases();
		for (int i = 0; i < cases.size(); i++) {
			List<PlusCalStatement> aCase = cases.get(i);
			TemporaryBinding.Checkpoint checkpoint = writeTemporaryBinding.checkpoint();
			Map<UID, TLAGeneralIdentifier> touchedVars = writeTemporaryBinding.startRecording();
			transformedCases.add(substituteBlock(aCase));
			writeTemporaryBinding.stopRecording();
			if (i != cases.size() - 1) {
				// only restore checkpoint if it's not the last case, so that the state of writeTemporaryBinding is
				// correct after translating this either statement
				writeTemporaryBinding.restore(checkpoint);
			}
			writesList.add(touchedVars);
		}
		Map<UID, TLAGeneralIdentifier> touchedVars = new LinkedHashMap<>();
		for (Map<UID, TLAGeneralIdentifier> uids : writesList) {
			declareJoinNames(location, uids, touchedVars);
		}
		for (int i = 0; i < transformedCases.size(); i++) {
			List<PlusCalStatement> transformedCase = transformedCases.get(i);
			Map<UID, TLAGeneralIdentifier> writes = writesList.get(i);
			transformedCases.set(i, writeJoinAssignments(location, touchedVars, writes, transformedCase));
		}
		return Collections.singletonList(new PlusCalEither(location, transformedCases));
	}

	private void assignmentHelper(SourceLocation location, TLAExpression lhs, TLAExpression rhs,
	                              List<PlusCalStatement> result) {
		TLAExpression transformedLHS = lhs.accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result));
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
					registry, params, arguments, expressionArguments, mappings, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander, result);
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
					registry, params, arguments, expressionArguments, mappings, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander, result)));
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
			if (!arguments.containsKey(varUID)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			TLAGeneralIdentifier dollarVariable = arguments.get(varUID);
			String nameHint = params.get(varUID).getName().getValue() + "Write";
			PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> writeVisitor;
			if (lhs instanceof TLAFunctionCall) {
				TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
						registry, params, arguments, expressionArguments, mappings, functionMappedVars,
						readTemporaryBinding, writeTemporaryBinding, procedureExpander, result);
				for (int j = accumulatedIndices.size() - 1; j >= 0; j--) {
					accumulatedIndices.set(j, accumulatedIndices.get(j).accept(visitor));
				}
				if (!mappings.containsKey(varUID)) {
					TLAFunctionSubstitution sub = new TLAFunctionSubstitution(
							location,
							writeTemporaryBinding.lookup(varUID).orElse(dollarVariable),
							Collections.singletonList(new TLAFunctionSubstitutionPair(
									location,
									Collections.singletonList(new TLASubstitutionKey(
											location, accumulatedIndices)),
									rhs)));
					TLAGeneralIdentifier temp = writeTemporaryBinding.declare(location, varUID, nameHint);
					result.add(new PlusCalAssignment(
							location, Collections.singletonList(new PlusCalAssignmentPair(location, temp, sub))));
					continue;
				}
				TLAExpression index = functionMappedVars.contains(varUID) ? accumulatedIndices.get(0) : null;
				writeVisitor = new ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor(
						registry, params, arguments, mappings, expressionArguments, functionMappedVars,
						readTemporaryBinding, writeTemporaryBinding, procedureExpander, dollarVariable, varUID,
						nameHint, index, accumulatedIndices,
						new TLAExpressionMappingMacroWriteExpansionVisitor(
								registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, rhs, varUID,
								index));
			} else {
				if (!mappings.containsKey(varUID)) {
					TLAGeneralIdentifier temp = writeTemporaryBinding.declare(location, varUID, nameHint);
					result.add(new PlusCalAssignment(
							location,
							Collections.singletonList(new PlusCalAssignmentPair(location, temp, rhs))));
					continue;
				}
				writeVisitor = new ModularPlusCalMappingMacroVariableWriteExpansionVisitor(
						registry, params, arguments, mappings, expressionArguments, functionMappedVars,
						readTemporaryBinding, writeTemporaryBinding, procedureExpander, dollarVariable, varUID,
						nameHint, null,
						new TLAExpressionMappingMacroWriteExpansionVisitor(
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
		TLAExpressionPlusCalCodeGenVisitor visitor = new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result);
		// the call has to be expanded before we insert the write-backs
		PlusCalCall expandedCall = procedureExpander.expand(plusCalCall, visitor);
		result.addAll(WriteBackInsertionVisitor.insertWriteBacks(
				result, getWriteBacksAndCleanUp(plusCalCall.getLocation())));
		// after inserting the write-backs, we can now safely insert the call
		result.add(expandedCall);
		// so now, the result looks like
		//
		// reads...
		// write-backs...
		// call Proc(args...)
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
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result);
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
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result));
		result.add(new PlusCalPrint(plusCalPrint.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalAssert.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result));
		result.add(new PlusCalAssert(plusCalAssert.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalAwait.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, result));
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
