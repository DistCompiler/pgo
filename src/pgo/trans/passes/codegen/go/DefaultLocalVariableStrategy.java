package pgo.trans.passes.codegen.go;

import pgo.model.golang.GoExpression;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.builder.GoBlockBuilder;
import pgo.scope.UID;
import pgo.trans.passes.codegen.go.GlobalVariableStrategy.GlobalVariableWrite;

public class DefaultLocalVariableStrategy extends LocalVariableStrategy {
    public void actionPrelude(GoBlockBuilder builder, UID labelUID) {
        // nothing to do
    }

    public GoExpression readLocalVariable(GoBlockBuilder builder, UID local) {
        return builder.findUID(local);
    }

    public GlobalVariableWrite writeLocalVariable(GoBlockBuilder builder, UID local) {
        GoVariableName name = builder.findUID(local);

        return new GlobalVariableWrite() {
            @Override
            public GoExpression getValueSink(GoBlockBuilder builder) {
                return name;
            }
            @Override
            public void writeAfter(GoBlockBuilder builder) {
                // pass
            }
        };
    }

    public void actionPostlude(GoBlockBuilder builder, UID labelUID) {
        // nothing to do
    }

}
