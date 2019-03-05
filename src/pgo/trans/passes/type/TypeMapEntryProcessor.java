package pgo.trans.passes.type;

import pgo.model.type.*;
import pgo.util.UnionFind;

import java.util.*;

public class TypeMapEntryProcessor {
	private final Set<TypeVariable> unresolvedVariables = new HashSet<>();
	private final Map<TypeVariable, Type> additionalMappings = new HashMap<>();
	private final TypeVariableCollectionVisitor collector =
			new TypeVariableCollectionVisitor(unresolvedVariables);
	private final TypeVariableSubstitutionVisitor subs = new TypeVariableSubstitutionVisitor(
			new TypeSubstitution(new UnionFind<>(), additionalMappings));
	private final InterfaceType pGoInterfaceType = new InterfaceType(Collections.emptyList());

	public Type process(TypeSubstitution substitution, TypeVariable typeVariable) {
		Type type;
		if (substitution.containsKey(typeVariable)) {
			type = substitution.get(typeVariable);
		} else {
			type = pGoInterfaceType;
			additionalMappings.put(typeVariable, pGoInterfaceType);
		}
		type.accept(collector);
		for (TypeVariable unresolvedVariable : unresolvedVariables) {
			additionalMappings.put(unresolvedVariable, pGoInterfaceType);
		}
		unresolvedVariables.clear();
		return type.accept(subs);
	}
}
