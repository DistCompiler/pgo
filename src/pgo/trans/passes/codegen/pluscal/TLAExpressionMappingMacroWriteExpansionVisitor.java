package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.List;
import java.util.Map;
import java.util.Set;

public class TLAExpressionMappingMacroWriteExpansionVisitor extends TLAExpressionMappingMacroReadExpansionVisitor {
	private final TLAExpression dollarValue;

	TLAExpressionMappingMacroWriteExpansionVisitor(
			DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
			Map<UID, TLAGeneralIdentifier> arguments, Set<UID> expressionArguments,
			Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> functionMappedVars,
			TemporaryBinding readTemporaryBinding, TemporaryBinding writeTemporaryBinding,
			ProcedureExpander procedureExpander, List<PlusCalStatement> output, TLAGeneralIdentifier dollarVariable,
			TLAExpression dollarValue, UID varUID, TLAExpression index) {
		super(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, output, dollarVariable, varUID, index);
		this.dollarValue = dollarValue;
	}

	@Override
	public TLAExpressionMappingMacroWriteExpansionVisitor createWith(List<PlusCalStatement> output) {
		return new TLAExpressionMappingMacroWriteExpansionVisitor(
				registry, params, arguments, expressionArguments, mappings, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, output, dollarVariable, dollarValue, varUID, index);
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) {
		return dollarValue;
	}
}
