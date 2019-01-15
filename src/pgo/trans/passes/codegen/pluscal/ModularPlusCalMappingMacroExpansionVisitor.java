package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.golang.NameCleaner;
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

public class ModularPlusCalMappingMacroExpansionVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	public interface YieldHandler {
		List<PlusCalStatement> handle(ModularPlusCalYield modularPlusCalYield);
	}

	private final DefinitionRegistry registry;
	private final NameCleaner nameCleaner;
	private final Map<UID, Set<UID>> labelUIDsToVarUIDs;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAExpression> boundValues;
	private final List<PlusCalVariableDeclaration> variables;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;
	private final YieldHandler yieldHandler;
	private final Map<UID, String> boundTemporaryVariables;

	private ModularPlusCalMappingMacroExpansionVisitor(DefinitionRegistry registry, NameCleaner nameCleaner,
	                                                   Map<UID, Set<UID>> labelUIDsToVarUIDs,
	                                                   Map<UID, PlusCalVariableDeclaration> arguments,
	                                                   Map<UID, TLAExpression> boundValues,
	                                                   List<PlusCalVariableDeclaration> variables,
	                                                   Map<UID, ModularPlusCalMappingMacro> mappings,
	                                                   Supplier<TLAGeneralIdentifier> dollarVariable,
	                                                   Supplier<TLAExpression> dollarValue,
	                                                   YieldHandler yieldHandler,
	                                                   Map<UID, String> boundTemporaryVariables) {
		this.registry = registry;
		this.nameCleaner = nameCleaner;
		this.labelUIDsToVarUIDs = labelUIDsToVarUIDs;
		this.arguments = arguments;
		this.boundValues = boundValues;
		this.variables = variables;
		this.mappings = mappings;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
		this.yieldHandler = yieldHandler;
		this.boundTemporaryVariables = boundTemporaryVariables;
	}

	ModularPlusCalMappingMacroExpansionVisitor(DefinitionRegistry registry, NameCleaner nameCleaner,
	                                           Map<UID, Set<UID>> labelUIDsToVarUIDs,
	                                           Map<UID, PlusCalVariableDeclaration> arguments,
	                                           Map<UID, TLAExpression> boundValues,
	                                           List<PlusCalVariableDeclaration> variables,
	                                           Map<UID, ModularPlusCalMappingMacro> mappings) {
		this(
				registry,
				nameCleaner,
				labelUIDsToVarUIDs,
				arguments,
				boundValues,
				variables,
				mappings,
				() -> { throw new Unreachable(); },
				() -> { throw new Unreachable(); },
				ignored -> { throw new Unreachable(); },
				new HashMap<>());
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		UID labelUID = labeledStatements.getLabel().getUID();
		SourceLocation labelLocation = labeledStatements.getLabel().getLocation();
		List<PlusCalStatement> statements = new ArrayList<>();
		// prefetch the variable values
		if (labelUIDsToVarUIDs.containsKey(labelUID)) {
			for (UID varUID : labelUIDsToVarUIDs.get(labelUID)) {
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
				TLAGeneralIdentifier temp = registry.defineTemporaryLocalVariable(
						labelLocation, nameCleaner, arguments.get(varUID).getName().getValue() + "Read", variables);
				boundTemporaryVariables.put(varUID, temp.getName().getId());
				if (mappingsContainsValue) {
					ModularPlusCalMappingMacroExpansionVisitor visitor = new ModularPlusCalMappingMacroExpansionVisitor(
							registry, nameCleaner, labelUIDsToVarUIDs, arguments, boundValues, variables, mappings,
							() -> variable,
							dollarValue,
							modularPlusCalYield -> {
								List<PlusCalStatement> result = new ArrayList<>();
								TLAExpression expression = modularPlusCalYield.getExpression().accept(
										new TLAExpressionMappingMacroExpansionVisitor(
												registry,
												() -> variable, dollarValue, boundTemporaryVariables));
								result.add(new PlusCalAssignment(
										modularPlusCalYield.getLocation(),
										Collections.singletonList(
												new PlusCalAssignmentPair(
														modularPlusCalYield.getLocation(), temp, expression))));
								return result;
							},
							boundTemporaryVariables);
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
		statements.addAll(substituteStatements(labeledStatements.getStatements()));
		// clean up and write back the written values for non-macro-mapped variables
		if (labelUIDsToVarUIDs.containsKey(labelUID)) {
			for (UID varUID : labelUIDsToVarUIDs.get(labelUID)) {
				// only write back non-macro-mapped refs
				TLAExpression value = boundValues.get(varUID);
				if (value instanceof TLARef) {
					UID valueUID = registry.followReference(value.getUID());
					if (!mappings.containsKey(valueUID)) {
						TLAGeneralIdentifier lhs = new TLAGeneralIdentifier(
								labelLocation,
								new TLAIdentifier(labelLocation, ((TLARef) value).getTarget()),
								Collections.emptyList());
						TLAGeneralIdentifier rhs = new TLAGeneralIdentifier(
								labelLocation,
								new TLAIdentifier(labelLocation, boundTemporaryVariables.get(varUID)),
								Collections.emptyList());
						statements.add(new PlusCalAssignment(
								labelLocation,
								Collections.singletonList(new PlusCalAssignmentPair(labelLocation, lhs, rhs))));
					}
				}
				boundTemporaryVariables.remove(varUID);
			}
		}
		return Collections.singletonList(new PlusCalLabeledStatements(
				labeledStatements.getLocation(),
				labeledStatements.getLabel(),
				statements));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalWhile.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
		result.add(new PlusCalWhile(
				plusCalWhile.getLocation(),
				condition,
				substituteStatements(plusCalWhile.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalIf.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
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
		TLAExpression transformedLHS = lhs.accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
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
				TLAGeneralIdentifier tempVariable = registry.defineTemporaryLocalVariable(
						location, nameCleaner, "rhsRead", variables);
				TLAExpression transformedRHS = rhs.accept(new TLAExpressionMappingMacroExpansionVisitor(
						registry, dollarVariable, dollarValue, boundTemporaryVariables));
				result.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(location, tempVariable, transformedRHS))));
				rhsList.add(tempVariable);
			}
		} else {
			// otherwise, don't create temporary variable for cleaner code
			rhsList.add(pairs.get(0).getRhs().accept(new TLAExpressionMappingMacroExpansionVisitor(
					registry, dollarVariable, dollarValue, boundTemporaryVariables)));
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
			ModularPlusCalMappingMacroExpansionVisitor visitor = new ModularPlusCalMappingMacroExpansionVisitor(
					registry, nameCleaner, labelUIDsToVarUIDs, arguments, boundValues, variables, mappings,
					() -> variable, () -> rhs,
					modularPlusCalYield -> {
						List<PlusCalStatement> res = new ArrayList<>();
						TLAExpression expression = modularPlusCalYield.getExpression().accept(
								new TLAExpressionMappingMacroExpansionVisitor(
										registry, () -> variable, () -> rhs, boundTemporaryVariables));
						res.add(new PlusCalAssignment(
								modularPlusCalYield.getLocation(),
								Collections.singletonList(new PlusCalAssignmentPair(
										modularPlusCalYield.getLocation(), variable, expression))));
						return res;
					},
					boundTemporaryVariables);
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
	public List<PlusCalStatement> visit(PlusCalSkip skip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(skip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<TLAExpression> args = new ArrayList<>();
		for (TLAExpression argument : plusCalCall.getArguments()) {
			args.add(argument.accept(new TLAExpressionMappingMacroExpansionVisitor(
					registry, dollarVariable, dollarValue, boundTemporaryVariables)));
		}
		result.add(new PlusCalCall(plusCalCall.getLocation(), plusCalCall.getTarget(), args));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith with) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<PlusCalVariableDeclaration> declarations = new ArrayList<>();
		for (PlusCalVariableDeclaration declaration : with.getVariables()) {
			declarations.add(new PlusCalVariableDeclaration(
					declaration.getLocation(),
					declaration.getName(),
					false,
					declaration.isSet(),
					declaration.getValue().accept(new TLAExpressionMappingMacroExpansionVisitor(
							registry, dollarVariable, dollarValue, boundTemporaryVariables))));
		}
		result.add(new PlusCalWith(with.getLocation(), declarations, substituteStatements(with.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalPrint.getValue().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
		result.add(new PlusCalPrint(plusCalPrint.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalAssert.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
		result.add(new PlusCalPrint(plusCalAssert.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalAwait.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, dollarVariable, dollarValue, boundTemporaryVariables));
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
