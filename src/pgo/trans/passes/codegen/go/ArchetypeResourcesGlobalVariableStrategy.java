package pgo.trans.passes.codegen.go;

import pgo.TODO;
import pgo.model.golang.*;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.golang.type.GoType;
import pgo.model.pcal.PlusCalProcess;
import pgo.scope.UID;

public class ArchetypeResourcesGlobalVariableStrategy extends GlobalVariableStrategy {
    public ArchetypeResourcesGlobalVariableStrategy() { }

    @Override
    public void initPostlude(GoModuleBuilder moduleBuilder, GoBlockBuilder initBuilder) {
        throw new TODO();
    }

    @Override
    public void processPrelude(GoBlockBuilder processBody, PlusCalProcess process, String processName, GoVariableName self, GoType selfType) {
        throw new TODO();
    }

    @Override
    public void mainPrelude(GoBlockBuilder builder) {
        throw new TODO();
    }

    @Override
    public void startCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        throw new TODO();
    }

    @Override
    public void abortCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        throw new TODO();
    }

    @Override
    public void endCriticalSection(GoBlockBuilder builder, UID processUID, int lockGroup, UID labelUID, GoLabelName labelName) {
        throw new TODO();
    }

    @Override
    public GoExpression readGlobalVariable(GoBlockBuilder builder, UID uid) {
        throw new TODO();
    }

    @Override
    public GlobalVariableWrite writeGlobalVariable(UID uid) {
        throw new TODO();
    }
}