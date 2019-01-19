package pgo.trans.passes.codegen.pluscal;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

public class TLAExpressionMappingMacroWriteExpansionVisitor extends TLAExpressionMappingMacroReadExpansionVisitor {
	private final TLAExpression dollarValue;

	public TLAExpressionMappingMacroWriteExpansionVisitor(DefinitionRegistry registry,
	                                                      TemporaryBinding readTemporaryBinding,
	                                                      TemporaryBinding writeTemporaryBinding,
	                                                      TLAExpression dollarVariable, TLAExpression dollarValue,
	                                                      UID varUID) {
		super(registry, readTemporaryBinding, writeTemporaryBinding, dollarVariable, varUID);
		this.dollarValue = dollarValue;
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) {
		return dollarValue;
	}
}
