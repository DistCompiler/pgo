package pgo.trans.passes.type;

import pgo.model.type.*;
import pgo.util.UnionFind;

import java.util.*;

public class TypeMapEntryProcessor {
	private final Set<PGoTypeVariable> unresolvedVariables = new HashSet<>();
	private final Map<PGoTypeVariable, PGoType> additionalMappings = new HashMap<>();
	private final PGoTypeVariableCollectionVisitor collector =
			new PGoTypeVariableCollectionVisitor(unresolvedVariables);
	private final PGoTypeVariableSubstitutionVisitor subs =
			new PGoTypeVariableSubstitutionVisitor(new PGoTypeSubstitution(new UnionFind<>(), additionalMappings));
	private final PGoTypeInterface pGoTypeInterface = new PGoTypeInterface(Collections.emptyList());

	public PGoType process(PGoTypeSubstitution substitution, PGoTypeVariable typeVariable) {
		PGoType type;
		if (substitution.containsKey(typeVariable)) {
			type = substitution.get(typeVariable);
		} else {
			type = pGoTypeInterface;
			additionalMappings.put(typeVariable, pGoTypeInterface);
		}
		type.accept(collector);
		for (PGoTypeVariable unresolvedVariable : unresolvedVariables) {
			additionalMappings.put(unresolvedVariable, pGoTypeInterface);
		}
		unresolvedVariables.clear();
		return type.accept(subs);
	}
}
