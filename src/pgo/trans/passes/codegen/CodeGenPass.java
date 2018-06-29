package pgo.trans.passes.codegen;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.Unreachable;
import pgo.model.golang.GoModule;
import pgo.model.golang.builder.GoModuleBuilder;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalProcesses;
import pgo.model.pcal.PlusCalSingleProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.GlobalVariableStrategy;
import pgo.trans.intermediate.SingleThreadedProcessGlobalVariableStrategy;

import java.util.Map;

public class CodeGenPass {
	private CodeGenPass() {}

	public static GoModule perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts,
								   PlusCalAlgorithm plusCalAlgorithm) {
		GoModuleBuilder moduleBuilder = new GoModuleBuilder(plusCalAlgorithm.getName().getValue());
		PlusCalProcesses processes = plusCalAlgorithm.getProcesses();
		GlobalVariableStrategy globalVariableStrategy;
		if (processes instanceof PlusCalSingleProcess) {
			globalVariableStrategy = new SingleThreadedProcessGlobalVariableStrategy();
		} else if (!opts.net.isEnabled()) {
			globalVariableStrategy = new MultithreadedProcessGlobalVariableStrategy(registry, typeMap, plusCalAlgorithm);
		} else {
			switch (opts.net.getStateOptions().strategy) {
				case PGoNetOptions.StateOptions.STATE_ETCD:
					globalVariableStrategy = new EtcdGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), plusCalAlgorithm);
					break;
				case PGoNetOptions.StateOptions.STATE_SERVER:
					globalVariableStrategy = new StateServerGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), plusCalAlgorithm);
					break;
				default:
					throw new Unreachable();
			}
		}
		processes.accept(new PlusCalProcessesCodeGenVisitor(
				registry, typeMap, globalVariableStrategy, plusCalAlgorithm, moduleBuilder));
		return moduleBuilder.getModule();
	}
}
