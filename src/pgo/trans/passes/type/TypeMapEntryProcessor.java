package pgo.trans.passes.type;

import pgo.model.type.*;
import pgo.scope.UID;

import java.util.*;

public class TypeMapEntryProcessor {
	private final Set<PGoTypeVariable> unresolvedVariables = new HashSet<>();
	private final Map<PGoTypeVariable, PGoType> additionalMappings = new HashMap<>();
	private final PGoTypeVariableCollectionVisitor collector =
			new PGoTypeVariableCollectionVisitor(unresolvedVariables);
	private final PGoTypeVariableSubstitutionVisitor substitution =
			new PGoTypeVariableSubstitutionVisitor(additionalMappings);
	private final PGoTypeInterface pGoTypeInterface = new PGoTypeInterface(Collections.emptyList());

	public PGoType process(Map<PGoTypeVariable, PGoType> typeMapping, UID uid, PGoTypeVariable typeVariable) {
		PGoType type;
		if (typeMapping.containsKey(typeVariable)) {
			type = typeMapping.get(typeVariable);
		} else {
			type = pGoTypeInterface;
			additionalMappings.put(typeVariable, pGoTypeInterface);
		}
		type.accept(collector);
		for (PGoTypeVariable unresolvedVariable : unresolvedVariables) {
			additionalMappings.put(unresolvedVariable, pGoTypeInterface);
		}
		unresolvedVariables.clear();
		return type.accept(substitution);
	}
}
