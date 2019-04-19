package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.PlusCalAssignment;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAExpressionVisitor;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ModularPlusCalMappingMacroVariableWriteExpansionVisitor
		extends ModularPlusCalMappingMacroReadExpansionVisitor {
	ModularPlusCalMappingMacroVariableWriteExpansionVisitor(
			DefinitionRegistry registry, Map<UID, PlusCalVariableDeclaration> params,
			Map<UID, TLAGeneralIdentifier> arguments,
			Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> expressionArguments,
			Set<UID> functionMappedVars, TemporaryBinding readTemporaryBinding,
			TemporaryBinding writeTemporaryBinding, ProcedureExpander procedureExpander,
			TLAExpressionPlusCalCodeGenVisitor visitor, TLAGeneralIdentifier dollarVariable, UID varUID,
			String nameHint, TLAExpression index) {
		super(
				registry, params, arguments, mappings, expressionArguments, functionMappedVars, readTemporaryBinding,
				writeTemporaryBinding, procedureExpander, dollarVariable, varUID, nameHint, index, visitor, null);
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
