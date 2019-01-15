package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

public class TLAExpressionMappingMacroExpansionVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;
	private final Map<UID, String> boundTemporaryVariables;

	public TLAExpressionMappingMacroExpansionVisitor(DefinitionRegistry registry,
	                                                 Supplier<TLAGeneralIdentifier> dollarVariable,
	                                                 Supplier<TLAExpression> dollarValue,
	                                                 Map<UID, String> boundTemporaryVariables) {
		this.registry = registry;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
		this.boundTemporaryVariables = boundTemporaryVariables;
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
		UID varUID = registry.followReference(pGoTLAVariable.getUID());
		if (boundTemporaryVariables.containsKey(varUID)) {
			return new TLAGeneralIdentifier(
					pGoTLAVariable.getLocation(),
					new TLAIdentifier(pGoTLAVariable.getLocation(), boundTemporaryVariables.get(varUID)),
					Collections.emptyList());
		}
		return pGoTLAVariable;
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
