package pgo.trans.passes.codegen.pluscal;

import pgo.model.mpcal.ModularPlusCalMappingMacro;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.scope.UID;

import java.util.List;
import java.util.Map;
import java.util.Set;

class ExpandedProcedureMatch {
	private final UID procedureUID;
	private final List<PlusCalVariableDeclaration> actualParams;
	private final Map<UID, TLAGeneralIdentifier> arguments;
	private final Map<UID, ModularPlusCalMappingMacro> mappings;
	private final Set<UID> refs;
	private final Set<UID> functionMappedVars;

	ExpandedProcedureMatch(UID procedureUID, List<PlusCalVariableDeclaration> actualParams,
	                       Map<UID, TLAGeneralIdentifier> arguments, Map<UID, ModularPlusCalMappingMacro> mappings,
	                       Set<UID> refs, Set<UID> functionMappedVars) {
		this.procedureUID = procedureUID;
		this.actualParams = actualParams;
		this.arguments = arguments;
		this.mappings = mappings;
		this.refs = refs;
		this.functionMappedVars = functionMappedVars;
	}

	@Override
	public int hashCode() {
		int result = 17;
		result = 31 * result + procedureUID.hashCode();
		result = 31 * result + actualParams.hashCode();
		result = 31 * result + arguments.hashCode();
		result = 31 * result + mappings.hashCode();
		result = 31 * result + refs.hashCode();
		result = 31 * result + functionMappedVars.hashCode();
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof ExpandedProcedureMatch)) {
			return false;
		}
		ExpandedProcedureMatch other = (ExpandedProcedureMatch) obj;
		return other.procedureUID.equals(procedureUID) &&
				other.actualParams.equals(actualParams) &&
				other.arguments.equals(arguments) &&
				other.mappings.equals(mappings) &&
				other.refs.equals(refs) &&
				other.functionMappedVars.equals(functionMappedVars);
	}
}
