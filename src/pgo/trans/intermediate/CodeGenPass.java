package pgo.trans.intermediate;

import java.util.Map;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.Unreachable;
import pgo.model.golang.Module;
import pgo.model.golang.ModuleBuilder;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.Processes;
import pgo.model.pcal.SingleProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.passes.codegen.EtcdGlobalVariableStrategy;
import pgo.trans.passes.codegen.MultithreadedProcessGlobalVariableStrategy;
import pgo.trans.passes.codegen.StateServerGlobalVariableStrategy;

public class CodeGenPass {
	private CodeGenPass() {}

	public static Module perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts,
	                             Algorithm algorithm) {
		ModuleBuilder moduleBuilder = new ModuleBuilder(algorithm.getName().getValue());
		Processes processes = algorithm.getProcesses();
		GlobalVariableStrategy globalVariableStrategy;
		if (processes instanceof SingleProcess) {
			globalVariableStrategy = new SingleThreadedProcessGlobalVariableStrategy();
		} else if (!opts.net.isEnabled()) {
			globalVariableStrategy = new MultithreadedProcessGlobalVariableStrategy(registry, typeMap, algorithm);
		} else {
			switch (opts.net.getStateOptions().strategy) {
				case PGoNetOptions.StateOptions.STATE_ETCD:
					globalVariableStrategy = new EtcdGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), algorithm);
					break;
				case PGoNetOptions.StateOptions.STATE_SERVER:
					globalVariableStrategy = new StateServerGlobalVariableStrategy(
							registry, typeMap, opts.net.getStateOptions(), algorithm);
					break;
				default:
					throw new Unreachable();
			}
		}
		processes.accept(new PlusCalProcessesCodeGenVisitor(
				registry, typeMap, globalVariableStrategy, algorithm, moduleBuilder));
		return moduleBuilder.getModule();
	}
}
