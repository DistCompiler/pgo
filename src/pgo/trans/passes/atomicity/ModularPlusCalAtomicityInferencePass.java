package pgo.trans.passes.atomicity;

import pgo.InternalCompilerError;
import pgo.Unreachable;
import pgo.model.mpcal.*;
import pgo.model.tla.*;
import pgo.util.UnionFind;
import pgo.model.pcal.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;

public class ModularPlusCalAtomicityInferencePass {
    private ModularPlusCalAtomicityInferencePass() {}

    private static void trackResource(DefinitionRegistry registry, Map<String, Boolean> mappings, Map<TLAExpression, UID> representativesMap, Map<UID, Set<UID>> map, TLAExpression expression, UID labelUID) {
        boolean track = false;

        if (expression instanceof TLAGeneralIdentifier) {
            String id = ((TLAGeneralIdentifier) expression).getName().getId();

            // if the name is a resource and is *not* function-mapped, it needs
            // to be tracked.
            if (mappings.containsKey(id) && !mappings.get(id)) {
                track = true;
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
            representativesMap.putIfAbsent(expression, expression.getUID());
            UID representative = representativesMap.get(expression);

            map.putIfAbsent(representative, new HashSet<>());
            map.get(representative).add(labelUID);
        }
    }

    private static void addToUnionFind(UnionFind<UID> unionFind, Map<UID, Set<UID>> map) {
        for (Map.Entry<UID, Set<UID>> entry : map.entrySet()) {
            UID varUID = entry.getKey();
            for (UID labelUID : entry.getValue()) {
                unionFind.union(labelUID, varUID);
            }
        }
    }

    public static void perform(DefinitionRegistry registry, ModularPlusCalBlock modularPlusCalBlock) {
        int lockGroups = 0;

        for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            Map<UID, Set<UID>> resourceReadsToLabel = new HashMap<>();
            Map<UID, Set<UID>> resourceWritesToLabel = new HashMap<>();
            Map<TLAExpression, UID> representativesMap = new HashMap<>();
            Map<String, Boolean> mappings = new HashMap<>();

            // build a map from resource's name to whether they are function mapped or not
            // By default, every archetype resource is non-function mapped
            archetype.getParams().forEach(p -> mappings.put(p.getName().getValue(), false));

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
                        mappings.put(archetype.getParams().get(pos).getName().getValue(), m.getVariable().isFunctionCall());
                    }
                }
            }

            BiConsumer<TLAExpression, UID> captureLabelRead = (expression, labelUID) ->
                    trackResource(registry, mappings, representativesMap, resourceReadsToLabel, expression, labelUID);

            BiConsumer<TLAExpression, UID> captureLabelWrite = (expression, labelUID) ->
                    trackResource(registry, mappings,representativesMap, resourceWritesToLabel, expression, labelUID);

            Set<UID> foundLabels = new HashSet<>();
            for (PlusCalStatement statement : archetype.getBody()) {
                statement.accept(new PlusCalStatementAtomicityInferenceVisitor(
                        new UID(), captureLabelRead, captureLabelWrite, foundLabels));
            }

            UnionFind<UID> unionFind = new UnionFind<>();
            addToUnionFind(unionFind, resourceReadsToLabel);
            addToUnionFind(unionFind, resourceWritesToLabel);
            Map<UID, Integer> seenRoots = new HashMap<>();
            for (UID labelUID : foundLabels) {
                if (unionFind.getRank(labelUID) > 0) {
                    UID rootUID = unionFind.find(labelUID);
                    if (!seenRoots.containsKey(rootUID)) {
                        seenRoots.put(rootUID, seenRoots.size());
                    }
                    registry.addLabelToLockGroup(labelUID, seenRoots.get(rootUID) + lockGroups);
                }
            }


            Map<UID, TLAExpression> representativeToExpression = representativesMap
                    .entrySet()
                    .stream()
                    .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));

            for (UID expUID : representativeToExpression.keySet()) {
                if (unionFind.getRank(expUID) > 0) {
                    int lockGroup = seenRoots.get(unionFind.find(expUID)) + lockGroups;
                    boolean isRead = resourceReadsToLabel.getOrDefault(expUID, Collections.emptySet())
                            .stream()
                            .map(registry::getLockGroup)
                            .anyMatch(i -> i.equals(lockGroup));
                    boolean isWritten = resourceWritesToLabel.getOrDefault(expUID, Collections.emptySet())
                            .stream()
                            .map(registry::getLockGroup)
                            .anyMatch(i -> i.equals(lockGroup));
                    if (!isRead && !isWritten) {
                        throw new InternalCompilerError();
                    }
                    if (isRead) {
                        registry.addResourceReadToLockGroup(representativeToExpression.get(expUID), lockGroup);
                    }
                    if (isWritten) {
                        registry.addResourceWriteToLockGroup(representativeToExpression.get(expUID), lockGroup);
                    }
                }
            }

            lockGroups += seenRoots.size();
        }
    }
}