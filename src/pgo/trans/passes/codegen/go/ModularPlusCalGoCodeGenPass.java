package pgo.trans.passes.codegen.go;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.GoModule;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalProcesses;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;

public class ModularPlusCalGoCodeGenPass {
    private ModularPlusCalGoCodeGenPass() {}

    public static GoModule perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts,
                                   ModularPlusCalBlock modularPlusCalBlock) {
        throw new TODO();
    }
}