package pgo.trans.passes.type;

import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.Type;
import pgo.model.type.TypeGenerator;
import pgo.model.type.TypeSolver;
import pgo.model.type.TypeVariable;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;
import java.util.Set;
import java.util.function.Function;

public class ArchetypeBodyExpressionTypeConstraintVisitor extends TLAExpressionTypeConstraintVisitor {
	private final Function<UID, Type> getValueType;
	private final Set<UID> paramUIDs;

	public ArchetypeBodyExpressionTypeConstraintVisitor(DefinitionRegistry registry, TypeSolver solver,
	                                                    TypeGenerator generator, Map<UID, TypeVariable> mapping,
	                                                    Function<UID, Type> getValueType, Set<UID> paramUIDs) {
		super(registry, solver, generator, mapping);
		this.getValueType = getValueType;
		this.paramUIDs = paramUIDs;
	}

	@Override
	public Type visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (paramUIDs.contains(varUID)) {
			return getValueType.apply(varUID);
		}
		return super.visit(tlaGeneralIdentifier);
	}
}
