package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor
		extends ModularPlusCalMappingMacroReadExpansionVisitor {
	private final List<TLAExpression> indices;

	public ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor(
			TemporaryBinding readTemporaryBinding, TemporaryBinding writeTemporaryBinding, TLAExpression dollarVariable,
			UID varUID, String nameHint, List<TLAExpression> indices,
			TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		super(readTemporaryBinding, writeTemporaryBinding, dollarVariable, varUID, nameHint, visitor);
		this.indices = indices;
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		SourceLocation location = modularPlusCalYield.getLocation();
		Optional<TLAGeneralIdentifier> optionalIdentifier = writeTemporaryBinding.lookup(varUID);
        TLAExpression var = optionalIdentifier.isPresent() ? optionalIdentifier.get() : dollarVariable;
		// yieldExpr has to be translated before the new temporary variable is declared in order for any $variable
		// references in it to be translated to a previous reference of $variable
		TLAExpression translatedYieldExpr = modularPlusCalYield.getExpression().accept(visitor);
		// the real yield expression is a function substitution
		TLAExpression yieldExpr = new TLAFunctionSubstitution(
				location,
				var,
				Collections.singletonList(new TLAFunctionSubstitutionPair(
						location,
						Collections.singletonList(new TLASubstitutionKey(location, indices)),
						translatedYieldExpr)));
		TLAGeneralIdentifier temp = writeTemporaryBinding.declare(modularPlusCalYield.getLocation(), varUID, nameHint);
		return Collections.singletonList(new PlusCalAssignment(
				modularPlusCalYield.getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						modularPlusCalYield.getLocation(), temp, yieldExpr))));
	}
}
