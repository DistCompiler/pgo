package pgo.trans.passes.codegen.go;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
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

public class PlusCalGoCodeGenPass {
	private PlusCalGoCodeGenPass() {}

	public static GoModule perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts,
	                               ModularPlusCalBlock modularPlusCalBlock) {
		GoModuleBuilder moduleBuilder = new GoModuleBuilder(modularPlusCalBlock.getName().getValue(), "main");
		PlusCalProcesses processes = modularPlusCalBlock.getProcesses();
		GlobalVariableStrategy globalVariableStrategy;
		if (processes instanceof PlusCalSingleProcess) {
			globalVariableStrategy = new SingleThreadedProcessGlobalVariableStrategy();
		} else if (!opts.net.isEnabled()) {
			globalVariableStrategy = new MultithreadedProcessGlobalVariableStrategy(
					registry, typeMap, modularPlusCalBlock);
		} else {
			switch (opts.net.getStateOptions().strategy) {
				case PGoNetOptions.StateOptions.STATE_ETCD:
					globalVariableStrategy = new EtcdGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), modularPlusCalBlock);
					break;
				case PGoNetOptions.StateOptions.STATE_SERVER:
					globalVariableStrategy = new StateServerGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), modularPlusCalBlock);
					break;
				default:
					throw new Unreachable();
			}
		}
		processes.accept(new PlusCalProcessesCodeGenVisitor(
				registry, typeMap, globalVariableStrategy, modularPlusCalBlock, moduleBuilder));
		return moduleBuilder.getModule();
	}
}
