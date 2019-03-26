package pgo.trans.passes.codegen.go;

import pgo.model.golang.GoExpression;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy.GlobalVariableWrite;

public abstract class LocalVariableStrategy {
    public abstract void actionPrelude(GoBlockBuilder builder);
    public abstract GoExpression readLocalVariable(GoBlockBuilder builder, UID local);
    public abstract GlobalVariableWrite writeLocalVariable(GoBlockBuilder builder, UID local);
    public abstract void actionPostlude(GoBlockBuilder builder);
}
