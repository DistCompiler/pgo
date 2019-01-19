package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAExpressionVisitor;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.scope.UID;

import java.util.Collections;
import java.util.List;

public class ModularPlusCalMappingMacroVariableWriteExpansionVisitor
		extends ModularPlusCalMappingMacroReadExpansionVisitor {
	ModularPlusCalMappingMacroVariableWriteExpansionVisitor(
			TemporaryBinding readTemporaryBinding, TemporaryBinding writeTemporaryBinding,
			TLAGeneralIdentifier dollarVariable, UID varUID, String nameHint, TLAExpression index,
			TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		super(readTemporaryBinding, writeTemporaryBinding, dollarVariable, varUID, nameHint, index, visitor, null);
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		// yieldExpr has to be translated before the new temporary variable is declared in order for any $variable
		// references in it to be translated to a previous reference of $variable
		TLAExpression yieldExpr = modularPlusCalYield.getExpression().accept(visitor);
		TLAGeneralIdentifier temp = writeTemporaryBinding.declare(modularPlusCalYield.getLocation(), varUID, nameHint);
		return Collections.singletonList(new PlusCalAssignment(
				modularPlusCalYield.getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						modularPlusCalYield.getLocation(), temp, yieldExpr))));
	}
}
