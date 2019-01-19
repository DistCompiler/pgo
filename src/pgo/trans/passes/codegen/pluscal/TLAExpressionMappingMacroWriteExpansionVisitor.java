package pgo.trans.passes.codegen.pluscal;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

public class TLAExpressionMappingMacroWriteExpansionVisitor extends TLAExpressionMappingMacroReadExpansionVisitor {
	private final TLAExpression dollarValue;

	TLAExpressionMappingMacroWriteExpansionVisitor(DefinitionRegistry registry, TemporaryBinding readTemporaryBinding,
	                                               TemporaryBinding writeTemporaryBinding,
	                                               TLAGeneralIdentifier dollarVariable, TLAExpression dollarValue,
	                                               UID varUID, TLAExpression index) {
		super(registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, varUID, index);
		this.dollarValue = dollarValue;
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) {
		return dollarValue;
	}
}
