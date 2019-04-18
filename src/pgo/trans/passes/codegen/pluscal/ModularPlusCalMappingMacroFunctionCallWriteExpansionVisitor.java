package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor
		extends ModularPlusCalMappingMacroReadExpansionVisitor {
	private final List<TLAExpression> indices;

	ModularPlusCalMappingMacroFunctionCallWriteExpansionVisitor(
			DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
			Map<UID, TLAGeneralIdentifier> arguments,
			Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> expressionArguments,
			Set<UID> functionMappedVars, TemporaryBinding readTemporaryBinding,
			TemporaryBinding writeTemporaryBinding, ProcedureExpander procedureExpander,
			TLAGeneralIdentifier dollarVariable, UID varUID, String nameHint, TLAExpression index,
			List<TLAExpression> indices, TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		super(
				registry, params, arguments, mappings, expressionArguments, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, dollarVariable, varUID, nameHint, index, visitor, null);
		this.indices = indices;
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		SourceLocation location = modularPlusCalYield.getLocation();
        TLAGeneralIdentifier var = writeTemporaryBinding.lookup(varUID).orElse(dollarVariable);
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
