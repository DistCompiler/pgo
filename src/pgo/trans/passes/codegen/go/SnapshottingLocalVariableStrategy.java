package pgo.trans.passes.codegen.go;

import pgo.model.golang.GoExpression;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.type.Type;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy.GlobalVariableWrite;

import java.util.HashMap;
import java.util.Map;

public class SnapshottingLocalVariableStrategy extends LocalVariableStrategy {
    private final DefinitionRegistry registry;
    private final Map<UID, Type> typeMap;
    private ModularPlusCalArchetype archetype;
    private final Map<UID, GoVariableName> localCopies;

    public SnapshottingLocalVariableStrategy(DefinitionRegistry registry, Map<UID, Type> typeMap) {
        this.registry = registry;
        this.typeMap = typeMap;
        this.localCopies = new HashMap<>();
    }

    public void initArchetype(GoBlockBuilder builder, ModularPlusCalArchetype archetype) {
        this.archetype = archetype;

        localCopies.clear();
        archetype.getVariables().forEach(var -> {
            GoType localType = typeMap.get(var.getUID()).accept(new TypeConversionVisitor());
            localCopies.put(var.getUID(), builder.varDecl(var.getName().getId() + "Copy", localType));
        });
    }

    public void actionPrelude(GoBlockBuilder builder, UID labelUID) {
        // Create a copy of each local variable used in this action
        registry.getLocalsInLabel(labelUID).forEach(local -> {
            GoVariableName goLocal = builder.findUID(local);
            GoType localType = typeMap.get(local).accept(new TypeConversionVisitor());

            GoVariableName copy = localType.accept(new CopyVisitor(builder, goLocal));
            GoVariableName dest = localCopies.get(local);

            builder.assign(dest, copy);
        });
    }

    public GoExpression readLocalVariable(GoBlockBuilder builder, UID local) {
        return localCopies.getOrDefault(local, builder.findUID(local));
    }

    public GlobalVariableWrite writeLocalVariable(GoBlockBuilder builder, UID local) {
        GoVariableName copy = localCopies.get(local);

        return new GlobalVariableWrite() {
            @Override
            public GoExpression getValueSink(GoBlockBuilder builder) {
                return copy;
            }
            @Override
            public void writeAfter(GoBlockBuilder builder) {
                // nothing to do
            }
        };
    }

    public void actionPostlude(GoBlockBuilder builder, UID labelUID) {
        // assign the original locals to their potentially modified copies
        registry.getLocalsInLabel(labelUID).forEach(local -> {
            GoVariableName goLocal = builder.findUID(local);
            builder.assign(goLocal, localCopies.get(local));
        });
    }

}
