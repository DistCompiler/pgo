package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAExpressionVisitor;
import pgo.trans.passes.codegen.TemporaryBinding;

import java.util.Collections;
import java.util.List;

public class ModularPlusCalMappingMacroWriteExpansionVisitor extends ModularPlusCalMappingMacroReadExpansionVisitor {
	public ModularPlusCalMappingMacroWriteExpansionVisitor(TemporaryBinding temporaryBinding, TLAExpression variable, TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		super(temporaryBinding, variable, visitor);
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssignment(
				modularPlusCalYield.getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						modularPlusCalYield.getLocation(),
						variable,
						modularPlusCalYield.getExpression().accept(visitor)))));
	}
}
