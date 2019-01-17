package pgo.trans.passes.codegen.pluscal;

import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLASpecialVariableValue;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.TemporaryBinding;

public class TLAExpressionMappingMacroWriteExpansionVisitor extends TLAExpressionMappingMacroReadExpansionVisitor {
	private final TLAExpression dollarValue;

	public TLAExpressionMappingMacroWriteExpansionVisitor(DefinitionRegistry registry,
	                                                      TemporaryBinding temporaryBinding,
	                                                      TLAExpression dollarVariable, TLAExpression dollarValue) {
		super(registry, temporaryBinding, dollarVariable);
		this.dollarValue = dollarValue;
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) {
		return dollarValue;
	}
}
