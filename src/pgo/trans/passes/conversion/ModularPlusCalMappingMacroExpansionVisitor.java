package pgo.trans.passes.conversion;

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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;
import java.util.stream.Collectors;

public class ModularPlusCalMappingMacroExpansionVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	public interface YieldHandler {
		List<PlusCalStatement> handle(ModularPlusCalYield modularPlusCalYield);
	}

	private final NameCleaner nameCleaner;
	private final DefinitionRegistry registry;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAExpression> boundValues;
	private final List<PlusCalVariableDeclaration> variables;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;
	private final YieldHandler yieldHandler;

	public ModularPlusCalMappingMacroExpansionVisitor(DefinitionRegistry registry, NameCleaner nameCleaner,
													  Map<UID, PlusCalVariableDeclaration> arguments,
													  Map<UID, TLAExpression> boundValues,
													  List<PlusCalVariableDeclaration> variables,
													  Map<UID, ModularPlusCalMappingMacro> mappings,
													  Supplier<TLAGeneralIdentifier> dollarVariable,
													  Supplier<TLAExpression> dollarValue,
													  YieldHandler yieldHandler) {
		this.nameCleaner = nameCleaner;
		this.registry = registry;
		this.arguments = arguments;
		this.boundValues = boundValues;
		this.variables = variables;
		this.mappings = mappings;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
		this.yieldHandler = yieldHandler;
	}

	public ModularPlusCalMappingMacroExpansionVisitor(DefinitionRegistry registry, NameCleaner nameCleaner,
													  Map<UID, PlusCalVariableDeclaration> arguments,
													  Map<UID, TLAExpression> boundValues,
													  List<PlusCalVariableDeclaration> variables,
													  Map<UID, ModularPlusCalMappingMacro> mappings) {
		this(
				registry,
				nameCleaner,
				arguments,
				boundValues,
				variables,
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
	public List<PlusCalStatement> visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		return Collections.singletonList(new PlusCalLabeledStatements(
				labeledStatements.getLocation(),
				labeledStatements.getLabel(),
				substituteStatements(labeledStatements.getStatements())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalWhile.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result));
		result.add(
				new PlusCalWhile(plusCalWhile.getLocation(), condition, substituteStatements(plusCalWhile.getBody())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression condition = plusCalIf.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result));
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
		TLAExpression transformedRHS = rhs.accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue,
				result));
		TLAExpression transformedLHS = lhs.accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue,
				result));
		result.add(new PlusCalAssignment(
                location,
				Collections.singletonList(new PlusCalAssignmentPair(location, transformedLHS, transformedRHS))));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
            TLAExpression lhs = pair.getLhs();
            if (!(lhs instanceof TLAGeneralIdentifier)) {
            	assignmentHelper(pair.getLocation(), lhs, pair.getRhs(), result);
            	continue;
			}
			UID uid = registry.followReference(lhs.getUID());
			if (!arguments.containsKey(uid)) {
				assignmentHelper(pair.getLocation(), lhs, pair.getRhs(), result);
                continue;
			}
			TLAExpression value = boundValues.get(uid);
			if (!(value instanceof TLAGeneralIdentifier) && !(value instanceof TLARef)) {
				assignmentHelper(pair.getLocation(), lhs, pair.getRhs(), result);
                continue;
			}
			TLAGeneralIdentifier variable = value instanceof TLARef
					? new TLAGeneralIdentifier(
					value.getLocation(),
					new TLAIdentifier(value.getLocation(), ((TLARef) value).getTarget()),
					Collections.emptyList())
					: (TLAGeneralIdentifier) value;
			UID valueUID = registry.followReference(value.getUID());
			// TODO the argument might have been renamed
			if (!mappings.containsKey(valueUID)) {
				assignmentHelper(pair.getLocation(), lhs, pair.getRhs(), result);
                continue;
			}
			ModularPlusCalMappingMacroExpansionVisitor visitor = new ModularPlusCalMappingMacroExpansionVisitor(
					registry, nameCleaner, arguments, boundValues, variables, mappings, () -> variable, pair::getRhs,
					modularPlusCalYield -> {
						List<PlusCalStatement> res = new ArrayList<>();
						TLAExpression expression = modularPlusCalYield.getExpression().accept(
								new TLAExpressionMappingMacroExpansionVisitor(
										registry, nameCleaner, arguments, boundValues, variables, mappings,
										() -> variable, pair::getRhs, res));
						res.add(new PlusCalAssignment(
								modularPlusCalYield.getLocation(),
								Collections.singletonList(new PlusCalAssignmentPair(
										modularPlusCalYield.getLocation(), variable, expression))));
						return res;
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
	public List<PlusCalStatement> visit(PlusCalSkip skip) throws RuntimeException {
        return Collections.singletonList(new PlusCalSkip(skip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		List<TLAExpression> args = new ArrayList<>();
		for (TLAExpression argument : plusCalCall.getArguments()) {
            args.add(argument.accept(new TLAExpressionMappingMacroExpansionVisitor(
            		registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result)));
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
							registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable,
							dollarValue, result))));
        }
        result.add(new PlusCalWith(with.getLocation(), declarations, substituteStatements(with.getBody())));
        return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
        List<PlusCalStatement> result = new ArrayList<>();
        TLAExpression expression = plusCalPrint.getValue().accept(new TLAExpressionMappingMacroExpansionVisitor(
        		registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result));
        result.add(new PlusCalPrint(plusCalPrint.getLocation(), expression));
        return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		TLAExpression expression = plusCalAssert.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result));
		result.add(new PlusCalPrint(plusCalAssert.getLocation(), expression));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
        TLAExpression condition = plusCalAwait.getCondition().accept(new TLAExpressionMappingMacroExpansionVisitor(
        		registry, nameCleaner, arguments, boundValues, variables, mappings, dollarVariable, dollarValue, result));
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
