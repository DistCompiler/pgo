package pgo.trans.passes.type;

import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;
import java.util.Set;
import java.util.function.Function;

public class ArchetypeBodyExpressionTypeConstraintVisitor extends TLAExpressionTypeConstraintVisitor {
	private final Function<UID, PGoType> getValueType;
	private final Set<UID> paramUIDs;

	public ArchetypeBodyExpressionTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver,
	                                                    PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping,
	                                                    Function<UID, PGoType> getValueType, Set<UID> paramUIDs) {
		super(registry, solver, generator, mapping);
		this.getValueType = getValueType;
		this.paramUIDs = paramUIDs;
	}

	@Override
	public PGoType visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (paramUIDs.contains(varUID)) {
			return getValueType.apply(varUID);
		}
		return super.visit(tlaGeneralIdentifier);
	}
}
