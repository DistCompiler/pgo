package pgo.trans.passes.atomicity;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.model.mpcal.*;
import pgo.model.tla.*;
import pgo.model.pcal.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

public class ModularPlusCalAtomicityInferencePass {
    private ModularPlusCalAtomicityInferencePass() {}

    private static void trackResource(DefinitionRegistry registry, Map<String, Boolean> mappings, Map<UID, Set<TLAExpression>> map, Set<UID> locals, TLAExpression expression, UID labelUID) {
        boolean track = false;

        if (expression instanceof TLAGeneralIdentifier) {
            String id = ((TLAGeneralIdentifier) expression).getName().getId();

            // if the name is a resource and is *not* function-mapped, it needs
            // to be tracked.
            if (mappings.containsKey(id)) {
                track = !mappings.get(id);
            } else {
                // track locals access per label
                UID ref = registry.followReference(expression.getUID());

                // only keep track of locals declared in the archetype. This filters
                // out short-lived local variables like the ones used in
                // set refinements or with statements.
                if (registry.isLocalVariable(ref) && locals.contains(ref)) {
                    registry.addLocalToLabel(labelUID, ref);
                }
            }

        } else if (expression instanceof TLAFunctionCall) {
            TLAExpression function = ((TLAFunctionCall) expression).getFunction();

            if (function instanceof TLAGeneralIdentifier) {
                String id = ((TLAGeneralIdentifier) function).getName().getId();

                // if the function is an archetype resource and *is* function
                // mapped, it needs to be tracked
                if (mappings.containsKey(id) && mappings.get(id)) {
                    track = true;
                }
            }
        } else {
            throw new InternalCompilerError();
        }

        if (track) {
            map.putIfAbsent(labelUID, new HashSet<>());
            map.get(labelUID).add(expression);
        }
    }

    public static void perform(DefinitionRegistry registry, ModularPlusCalBlock modularPlusCalBlock) {
        int lockGroups = 0;

        for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            Map<UID, Set<TLAExpression>> labelToResourceReads = new HashMap<>();
            Map<UID, Set<TLAExpression>> labelToResourceWrites = new HashMap<>();
            Map<String, Boolean> mappings = new HashMap<>();

            // build a map from resource's name to whether they are function mapped or not
            // By default, every archetype resource is non-function mapped
            archetype.getParams().forEach(p -> mappings.put(p.getName().getId(), false));

            // if there is one instantiation where a resource is function mapped, update
            // the mappings accordingly
            for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
                if (instance.getTarget().equals(archetype.getName())) {
                    Map<String, Integer> resourceVars = new HashMap<>();

                    ListIterator<TLAExpression> it = instance.getArguments().listIterator();
                    while (it.hasNext()) {
                        TLAExpression arg = it.next();

                        if (arg instanceof TLAGeneralIdentifier) {
                            String argName = ((TLAGeneralIdentifier) arg).getName().getId();
                            resourceVars.put(argName, it.nextIndex()-1);
                        } else if (arg instanceof TLARef) {
                            String refName = ((TLARef) arg).getTarget();
                            resourceVars.put(refName, it.nextIndex()-1);
                        }
                    }

                    for (ModularPlusCalMapping m : instance.getMappings()) {
                        int pos;
                        if (m.getVariable() instanceof ModularPlusCalMappingVariableName) {
                            pos = resourceVars.get(((ModularPlusCalMappingVariableName) m.getVariable()).getName());
                        } else if (m.getVariable() instanceof ModularPlusCalMappingVariablePosition) {
                            // position-mapping is 1-indexed
                            pos = ((ModularPlusCalMappingVariablePosition) m.getVariable()).getPosition() - 1;
                        } else {
                            throw new Unreachable();
                        }
                        mappings.put(archetype.getParams().get(pos).getName().getId(), m.getVariable().isFunctionCall());
                    }
                }
            }

            Set<UID> locals = archetype
                    .getVariables()
                    .stream()
                    .map(PlusCalVariableDeclaration::getUID)
                    .collect(Collectors.toSet());

            BiConsumer<TLAExpression, UID> captureLabelRead = (expression, labelUID) ->
                    trackResource(registry, mappings, labelToResourceReads, locals, expression, labelUID);

            BiConsumer<TLAExpression, UID> captureLabelWrite = (expression, labelUID) ->
                    trackResource(registry, mappings, labelToResourceWrites, locals, expression, labelUID);

            Set<UID> foundLabels = new HashSet<>();
            for (PlusCalStatement statement : archetype.getBody()) {
                statement.accept(new PlusCalStatementAtomicityInferenceVisitor(
                        new UID(), captureLabelRead, captureLabelWrite, foundLabels));
            }

            for (UID labelUID : foundLabels) {
                int lockGroup = lockGroups++;
                registry.addLabelToLockGroup(labelUID, lockGroup);

                labelToResourceReads.getOrDefault(labelUID, Collections.emptySet()).forEach(resource ->
                    registry.addResourceReadToLockGroup(resource, lockGroup)
                );

                labelToResourceWrites.getOrDefault(labelUID, Collections.emptySet()).forEach(resource ->
                        registry.addResourceWriteToLockGroup(resource, lockGroup)
                );
            }
        }
    }
}