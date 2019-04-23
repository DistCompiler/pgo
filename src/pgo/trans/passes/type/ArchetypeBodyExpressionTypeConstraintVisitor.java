package pgo.trans.passes.type;

import pgo.model.tla.TLAFunctionCall;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.type.*;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

public class ArchetypeBodyExpressionTypeConstraintVisitor extends TLAExpressionTypeConstraintVisitor {
	private final Set<UID> functionMappedParamUIDs;
	private final Set<UID> paramUIDs;

	public ArchetypeBodyExpressionTypeConstraintVisitor(DefinitionRegistry registry, TypeSolver solver,
	                                                    TypeGenerator generator, Map<UID, TypeVariable> mapping,
	                                                    Set<UID> functionMappedParamUIDs, Set<UID> paramUIDs) {
		super(registry, solver, generator, mapping);
		this.functionMappedParamUIDs = functionMappedParamUIDs;
		this.paramUIDs = paramUIDs;
	}

	@Override
	public Type visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		Type type = super.visit(tlaGeneralIdentifier);
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (paramUIDs.contains(varUID)) {
			TypeVariable returnType = generator.getTypeVariable(Collections.singletonList(tlaGeneralIdentifier));
			solver.addConstraint(new MonomorphicConstraint(
					tlaGeneralIdentifier,
					mapping.get(varUID),
					new ArchetypeResourceType(
							returnType,
							generator.getTypeVariable(Collections.singletonList(tlaGeneralIdentifier)),
							Collections.singletonList(tlaGeneralIdentifier))));
			mapping.put(tlaGeneralIdentifier.getUID(), returnType);
			return returnType;
		}
		return type;
	}

	@Override
	public Type visit(TLAFunctionCall tlaFunctionCall) {
		if (tlaFunctionCall.getParams().size() == 1 && tlaFunctionCall.getFunction() instanceof TLAGeneralIdentifier) {
			UID varUID = registry.followReference(tlaFunctionCall.getFunction().getUID());
			if (!functionMappedParamUIDs.contains(varUID)) {
				return super.visit(tlaFunctionCall);
			}
			mapping.put(tlaFunctionCall.getFunction().getUID(), mapping.get(varUID));
			Type returnType = generator.getTypeVariable(Collections.singletonList(tlaFunctionCall));
			solver.addConstraint(new MonomorphicConstraint(
					tlaFunctionCall,
					mapping.get(varUID),
					new ArchetypeResourceCollectionType(
							wrappedVisit(tlaFunctionCall.getParams().get(0)),
							returnType,
							generator.getTypeVariable(Collections.singletonList(tlaFunctionCall)),
							Collections.singletonList(tlaFunctionCall))));
			return returnType;
		}
		return super.visit(tlaFunctionCall);
	}
}
