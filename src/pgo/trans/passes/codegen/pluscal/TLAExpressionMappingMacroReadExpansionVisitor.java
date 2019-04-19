package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;

public class TLAExpressionMappingMacroReadExpansionVisitor extends TLAExpressionPlusCalCodeGenVisitor {
	protected final TLAGeneralIdentifier dollarVariable;
	protected final UID varUID;
	protected final TLAExpression index;

	TLAExpressionMappingMacroReadExpansionVisitor(
			DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
			Map<UID, TLAGeneralIdentifier> arguments, Set<UID> expressionArguments,
			Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> functionMappedVars,
			TemporaryBinding readTemporaryBinding, TemporaryBinding writeTemporaryBinding,
			ProcedureExpander procedureExpander, List<PlusCalStatement> output, TLAGeneralIdentifier dollarVariable,
			UID varUID, TLAExpression index) {
		super(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, output);
		this.dollarVariable = dollarVariable;
		this.varUID = varUID;
		this.index = index;
	}

	@Override
	public TLAExpressionMappingMacroReadExpansionVisitor createWith(List<PlusCalStatement> output) {
		return new TLAExpressionMappingMacroReadExpansionVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, output, dollarVariable, varUID, index);
	}

	private List<TLAExpression> substituteExpressions(List<TLAExpression> expressions) {
		List<TLAExpression> result = new ArrayList<>();
		for (TLAExpression expression : expressions) {
			result.add(expression.accept(this));
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		return new TLAFunctionCall(
				tlaFunctionCall.getLocation(),
				tlaFunctionCall.getFunction().accept(this),
				substituteExpressions(tlaFunctionCall.getParams()));
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
	public TLAExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		return readTemporaryBinding
				.lookup(registry.followReference(tlaGeneralIdentifier.getUID()))
				.orElse(tlaGeneralIdentifier);
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		Optional<TLAGeneralIdentifier> optionalResult = writeTemporaryBinding.lookup(varUID);
		if (optionalResult.isPresent() && index != null) {
			return new TLAFunctionCall(
					tlaSpecialVariableVariable.getLocation(), optionalResult.get(), Collections.singletonList(index));
		}
		if (optionalResult.isPresent()) {
			return optionalResult.get();
		}
		if (index != null) {
			return new TLAFunctionCall(
					tlaSpecialVariableVariable.getLocation(), dollarVariable, Collections.singletonList(index));
		}
		return dollarVariable;
	}
}
