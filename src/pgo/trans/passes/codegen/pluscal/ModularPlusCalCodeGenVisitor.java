package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.pcal.builder.TemporaryBinding;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

public class ModularPlusCalCodeGenVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	public interface YieldHandler {
		List<PlusCalStatement> handle(ModularPlusCalYield modularPlusCalYield);
	}

	private final DefinitionRegistry registry;
	private final TemporaryBinding temporaryBinding;
	private final boolean renameWithDeclarations;
	private final Map<UID, Set<UID>> labelsToVarReads;
	private final Map<UID, Set<UID>> labelsToVarWrites;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAExpression> boundValues;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;
	private final YieldHandler yieldHandler;

	private ModularPlusCalCodeGenVisitor(DefinitionRegistry registry, TemporaryBinding temporaryBinding,
	                                     boolean renameWithDeclarations,
	                                     Map<UID, Set<UID>> labelsToVarReads,
	                                     Map<UID, Set<UID>> labelsToVarWrites,
	                                     Map<UID, PlusCalVariableDeclaration> arguments,
	                                     Map<UID, TLAExpression> boundValues,
	                                     Map<UID, ModularPlusCalMappingMacro> mappings,
	                                     Supplier<TLAGeneralIdentifier> dollarVariable,
	                                     Supplier<TLAExpression> dollarValue,
	                                     YieldHandler yieldHandler) {
		this.registry = registry;
		this.temporaryBinding = temporaryBinding;
		this.renameWithDeclarations = renameWithDeclarations;
		this.labelsToVarReads = labelsToVarReads;
		this.labelsToVarWrites = labelsToVarWrites;
		this.arguments = arguments;
		this.boundValues = boundValues;
		this.mappings = mappings;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
		this.yieldHandler = yieldHandler;
	}

	ModularPlusCalCodeGenVisitor(DefinitionRegistry registry, TemporaryBinding temporaryBinding,
	                             Map<UID, Set<UID>> labelsToVarReads,
	                             Map<UID, Set<UID>> labelsToVarWrites,
	                             Map<UID, PlusCalVariableDeclaration> arguments,
	                             Map<UID, TLAExpression> boundValues,
	                             Map<UID, ModularPlusCalMappingMacro> mappings) {
		this(
				registry,
				temporaryBinding,
				false,
				labelsToVarReads,
				labelsToVarWrites,
				arguments,
				boundValues,
				mappings,
				() -> { throw new Unreachable(); },
				() -> { throw new Unreachable(); },
				ignored -> { throw new Unreachable(); });
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
		List<PlusCalStatement> statements = new ArrayList<>();
		// prefetch the variable values
		if (labelsToVarReads.containsKey(labelUID)) {
			for (UID varUID : labelsToVarReads.get(labelUID)) {
				TLAExpression value = boundValues.get(varUID);
				if (!(value instanceof TLAGeneralIdentifier) && !(value instanceof TLARef)) {
					continue;
				}
				TLAGeneralIdentifier variable = value instanceof TLARef
						? new TLAGeneralIdentifier(
							value.getLocation(),
							new TLAIdentifier(value.getLocation(), ((TLARef) value).getTarget()),
							Collections.emptyList())
						: (TLAGeneralIdentifier) value;
				UID valueUID = registry.followReference(value.getUID());
				boolean mappingsContainsValue = mappings.containsKey(valueUID);
				TLAGeneralIdentifier temp = temporaryBinding.declare(
						labelLocation,
						varUID,
						arguments.get(varUID).getName().getValue() + "Read");
				if (mappingsContainsValue) {
					ModularPlusCalCodeGenVisitor visitor = new ModularPlusCalCodeGenVisitor(
							registry, temporaryBinding, true, labelsToVarReads, labelsToVarWrites, arguments,
							boundValues, mappings, () -> variable, dollarValue,
							modularPlusCalYield -> {
								TLAExpression expression = modularPlusCalYield.getExpression().accept(
										new TLAExpressionPlusCalCodeGenVisitor(
												registry, temporaryBinding, () -> variable, dollarValue));
								return Collections.singletonList(new PlusCalAssignment(
										modularPlusCalYield.getLocation(),
										Collections.singletonList(
												new PlusCalAssignmentPair(
														modularPlusCalYield.getLocation(), temp, expression))));
							});
					for (PlusCalStatement statement : mappings.get(valueUID).getReadBody()) {
						statements.addAll(statement.accept(visitor));
					}
				} else {
					TLAExpression rhs = value instanceof TLARef
							? new TLAGeneralIdentifier(
								labelLocation,
								new TLAIdentifier(labelLocation, ((TLARef) value).getTarget()),
								Collections.emptyList())
							: value;
					statements.add(new PlusCalAssignment(
							labelLocation,
							Collections.singletonList(new PlusCalAssignmentPair(labelLocation, temp, rhs))));
				}
			}
		}
		// actually translate the statements in this labeledStatements
		statements.addAll(substituteStatements(plusCalLabeledStatements.getStatements()));
		// clean up and write back the written values for non-macro-mapped variables
		if (labelsToVarWrites.containsKey(labelUID)) {
			for (UID varUID : labelsToVarWrites.get(labelUID)) {
				// only write back non-macro-mapped refs
				TLAExpression value = boundValues.get(varUID);
				if (value instanceof TLARef) {
					UID valueUID = registry.followReference(value.getUID());
					if (!mappings.containsKey(valueUID)) {
						TLAGeneralIdentifier lhs = new TLAGeneralIdentifier(
								labelLocation,
								new TLAIdentifier(labelLocation, ((TLARef) value).getTarget()),
								Collections.emptyList());
						TLAGeneralIdentifier rhs = temporaryBinding.lookup(varUID).get();
						statements.add(new PlusCalAssignment(
								labelLocation,
								Collections.singletonList(new PlusCalAssignmentPair(labelLocation, lhs, rhs))));
					}
				}
				temporaryBinding.reuse(varUID);
			}
		}
		return Collections.singletonList(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(),
				statements));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalWhile.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
		result.add(new PlusCalWhile(
				plusCalWhile.getLocation(),
				condition,
				substituteStatements(plusCalWhile.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalIf.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
		result.add(new PlusCalIf(
				plusCalIf.getLocation(),
				condition,
				substituteStatements(plusCalIf.getYes()),
				substituteStatements(plusCalIf.getNo())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		return Collections.singletonList(new PlusCalEither(
				plusCalEither.getLocation(),
				plusCalEither.getCases().stream().map(this::substituteStatements).collect(Collectors.toList())));
	}

	private void assignmentHelper(SourceLocation location, TLAExpression lhs, TLAExpression rhs,
	                              List<PlusCalStatement> result) {
		TLAExpression transformedLHS = lhs.accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
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
			// read the RHS into temporary variables for use later so that parallel assignment works right
			for (PlusCalAssignmentPair pair : pairs) {
				SourceLocation location = pair.getLocation();
				TLAExpression rhs = pair.getRhs();
				TLAGeneralIdentifier tempVariable = temporaryBinding.declare(location, new UID(), "rhsRead");
				TLAExpression transformedRHS = rhs.accept(new TLAExpressionPlusCalCodeGenVisitor(
						registry, temporaryBinding, dollarVariable, dollarValue));
				result.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, tempVariable, transformedRHS))));
				rhsList.add(tempVariable);
			}
		} else {
			// otherwise, don't create temporary variable for cleaner code
			rhsList.add(pairs.get(0).getRhs().accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, temporaryBinding, dollarVariable, dollarValue)));
		}
		for (int i = 0; i < pairs.size(); i++) {
			PlusCalAssignmentPair pair = pairs.get(i);
			SourceLocation location = pair.getLocation();
			TLAExpression lhs = pair.getLhs();
			TLAExpression rhs = rhsList.get(i);
			if (!(lhs instanceof TLAGeneralIdentifier)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			UID uid = registry.followReference(lhs.getUID());
			if (!arguments.containsKey(uid)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			TLAExpression value = boundValues.get(uid);
			if (!(value instanceof TLAGeneralIdentifier) && !(value instanceof TLARef)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			TLAGeneralIdentifier variable = value instanceof TLARef
					? new TLAGeneralIdentifier(
						location,
						new TLAIdentifier(location, ((TLARef) value).getTarget()),
						Collections.emptyList())
					: (TLAGeneralIdentifier) value;
			UID valueUID = registry.followReference(value.getUID());
			// TODO the argument might have been renamed
			if (!mappings.containsKey(valueUID)) {
				assignmentHelper(location, lhs, rhs, result);
				continue;
			}
			ModularPlusCalCodeGenVisitor visitor = new ModularPlusCalCodeGenVisitor(
					registry, temporaryBinding, true, labelsToVarReads, labelsToVarWrites, arguments,
					boundValues, mappings, () -> variable, () -> rhs,
					modularPlusCalYield -> {
						TLAExpression expression = modularPlusCalYield.getExpression().accept(
								new TLAExpressionPlusCalCodeGenVisitor(
										registry, temporaryBinding, () -> variable, () -> rhs));
						return Collections.singletonList(new PlusCalAssignment(
								modularPlusCalYield.getLocation(),
								Collections.singletonList(new PlusCalAssignmentPair(
										modularPlusCalYield.getLocation(), variable, expression))));
					});
			for (PlusCalStatement statement : mappings.get(valueUID).getWriteBody()) {
				result.addAll(statement.accept(visitor));
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
		for (TLAExpression argument : plusCalCall.getArguments()) {
			args.add(argument.accept(new TLAExpressionPlusCalCodeGenVisitor(
					registry, temporaryBinding, dollarVariable, dollarValue)));
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
		for (PlusCalVariableDeclaration declaration : plusCalWith.getVariables()) {
			if (renameWithDeclarations) {
				TLAGeneralIdentifier fresh = temporaryBinding.freshVariable(
						declaration.getLocation(), declaration.getUID(), declaration.getName().getValue());
				declarations.add(new PlusCalVariableDeclaration(
						declaration.getLocation(),
						new Located<>(declaration.getName().getLocation(), fresh.getName().getId()),
						false,
						declaration.isSet(),
						declaration.getValue().accept(new TLAExpressionPlusCalCodeGenVisitor(
								registry, temporaryBinding, dollarVariable, dollarValue))));
			} else {
				declarations.add(new PlusCalVariableDeclaration(
						declaration.getLocation(),
						declaration.getName(),
						false,
						declaration.isSet(),
						declaration.getValue().accept(new TLAExpressionPlusCalCodeGenVisitor(
								registry, temporaryBinding, dollarVariable, dollarValue))));
			}
		}
		result.add(new PlusCalWith(plusCalWith.getLocation(), declarations, substituteStatements(plusCalWith.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalPrint.getValue().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
		result.add(new PlusCalPrint(plusCalPrint.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalAssert.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
		result.add(new PlusCalPrint(plusCalAssert.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalAwait.getCondition().accept(new TLAExpressionPlusCalCodeGenVisitor(
				registry, temporaryBinding, dollarVariable, dollarValue));
		result.add(new PlusCalAwait(plusCalAwait.getLocation(), condition));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(new PlusCalGoto(plusCalGoto.getLocation(), plusCalGoto.getTarget()));
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return yieldHandler.handle(modularPlusCalYield);
	}
}
