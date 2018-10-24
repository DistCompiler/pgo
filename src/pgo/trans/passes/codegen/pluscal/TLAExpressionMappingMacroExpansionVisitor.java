package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.NameCleaner;
import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

public class TLAExpressionMappingMacroExpansionVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final NameCleaner nameCleaner;
	private final Map<UID, PlusCalVariableDeclaration> arguments;
	private final Map<UID, TLAExpression> boundValues;
	private final List<PlusCalVariableDeclaration> variables;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;
	private final List<PlusCalStatement> output;

	public TLAExpressionMappingMacroExpansionVisitor(DefinitionRegistry registry, NameCleaner nameCleaner,
													 Map<UID, PlusCalVariableDeclaration> arguments,
													 Map<UID, TLAExpression> boundValues,
													 List<PlusCalVariableDeclaration> variables,
													 Map<UID, ModularPlusCalMappingMacro> mappings,
													 Supplier<TLAGeneralIdentifier> dollarVariable,
													 Supplier<TLAExpression> dollarValue,
													 List<PlusCalStatement> output) {
		this.registry = registry;
		this.nameCleaner = nameCleaner;
		this.arguments = arguments;
		this.boundValues = boundValues;
		this.variables = variables;
		this.mappings = mappings;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
		this.output = output;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : pGoTLAFunctionCall.getParams()) {
			arguments.add(argument.accept(this));
		}
		return new TLAFunctionCall(pGoTLAFunctionCall.getLocation(), pGoTLAFunctionCall.getFunction(), arguments);
	}

	@Override
	public TLAExpression visit(TLABinOp TLABinOp) throws RuntimeException {
		TLAExpression lhs = TLABinOp.getLHS().accept(this);
		TLAExpression rhs = TLABinOp.getRHS().accept(this);
        return new TLABinOp(TLABinOp.getLocation(), TLABinOp.getOperation(), TLABinOp.getPrefix(), lhs, rhs);
	}

	@Override
	public TLAExpression visit(TLABool TLABool) throws RuntimeException {
		return TLABool;
	}

	@Override
	public TLAExpression visit(TLACase TLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAExistential TLAExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAIf pGoTLAIf) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		UID uid = registry.followReference(pGoTLAVariable.getUID());
		if (!arguments.containsKey(uid)) {
			return pGoTLAVariable;
		}
		PlusCalVariableDeclaration argument = arguments.get(uid);
		TLAExpression value = boundValues.get(uid);
		if (!(value instanceof TLAGeneralIdentifier) && !(value instanceof TLARef)) {
			return pGoTLAVariable;
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
			return pGoTLAVariable;
		}
		String name = nameCleaner.cleanName(argument.getName().getValue() + "R");
		variables.add(new PlusCalVariableDeclaration(
				pGoTLAVariable.getLocation(),
				new Located<>(pGoTLAVariable.getLocation(), name),
				false,
				false,
				new PlusCalDefaultInitValue(pGoTLAVariable.getLocation())));
		TLAGeneralIdentifier temp = new TLAGeneralIdentifier(
				pGoTLAVariable.getLocation(),
				new TLAIdentifier(pGoTLAVariable.getLocation(), name),
				Collections.emptyList());
		ModularPlusCalMappingMacroExpansionVisitor visitor = new ModularPlusCalMappingMacroExpansionVisitor(
				registry, nameCleaner, arguments, boundValues, variables, mappings, () -> variable, dollarValue,
				modularPlusCalYield -> {
					List<PlusCalStatement> result = new ArrayList<>();
					TLAExpression expression = modularPlusCalYield.getExpression().accept(
							new TLAExpressionMappingMacroExpansionVisitor(
									registry, nameCleaner, arguments, boundValues, variables, mappings, () -> variable,
									dollarValue, result));
					result.add(new PlusCalAssignment(
							modularPlusCalYield.getLocation(),
							Collections.singletonList(
									new PlusCalAssignmentPair(modularPlusCalYield.getLocation(), temp, expression))));
					return result;
				});
		for (PlusCalStatement statement : mappings.get(valueUID).getReadBody()) {
			output.addAll(statement.accept(visitor));
		}
        return temp;
	}

	@Override
	public TLAExpression visit(TLATuple pGoTLATuple) throws RuntimeException {
		List<TLAExpression> elements = new ArrayList<>();
		for (TLAExpression expression : pGoTLATuple.getElements()) {
			elements.add(expression.accept(this));
		}
		return new TLATuple(pGoTLATuple.getLocation(), elements);
	}

	@Override
	public TLAExpression visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLANumber pGoTLANumber) throws RuntimeException {
        return pGoTLANumber;
	}

	@Override
	public TLAExpression visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : pGoTLAOperatorCall.getArgs()) {
			arguments.add(argument.accept(this));
		}
        return new TLAOperatorCall(
        		pGoTLAOperatorCall.getLocation(),
				pGoTLAOperatorCall.getName(),
				pGoTLAOperatorCall.getPrefix(),
				arguments);
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		List<TLAExpression> contents = new ArrayList<>();
		for (TLAExpression expression : pGoTLASetConstructor.getContents()) {
			contents.add(expression.accept(this));
		}
		return new TLASetConstructor(pGoTLASetConstructor.getLocation(), contents);
	}

	@Override
	public TLAExpression visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAString pGoTLAString) throws RuntimeException {
		return pGoTLAString;
	}

	@Override
	public TLAExpression visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		TLAExpression expression = pGoTLAUnary.getOperand().accept(this);
		return new TLAUnary(pGoTLAUnary.getLocation(), pGoTLAUnary.getOperation(), pGoTLAUnary.getPrefix(), expression);
	}

	@Override
	public TLAExpression visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue;
	}

	@Override
	public TLAExpression visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
        return dollarVariable.get();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
        return dollarValue.get().accept(this);
	}

	@Override
	public TLAExpression visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
