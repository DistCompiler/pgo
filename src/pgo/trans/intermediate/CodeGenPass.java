package pgo.trans.intermediate;

import java.util.Map;

import pgo.PGoNetOptions;
import pgo.PGoOptions;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.golang.Module;
import pgo.model.golang.ModuleBuilder;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.Processes;
import pgo.model.pcal.SingleProcess;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class CodeGenPass {
	private CodeGenPass() {}

	public static Module perform(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                             Map<UID, Integer> labelsToLockGroups, PGoOptions opts, Algorithm algorithm) {
		ModuleBuilder moduleBuilder = new ModuleBuilder(algorithm.getName());
		Processes processes = algorithm.getProcesses();
		GlobalVariableStrategy globalVariableStrategy;
		if (processes instanceof SingleProcess) {
			globalVariableStrategy = new SingleThreadedProcessGlobalVariableStrategy(registry, typeMap, algorithm);
		} else if (!opts.net.isEnabled()) {
			globalVariableStrategy = new MultithreadedProcessGlobalVariableStrategy(
					registry, typeMap, labelsToLockGroups, algorithm);
		} else {
			switch (opts.net.getStateOptions().strategy) {
				case PGoNetOptions.StateOptions.STATE_ETCD:
					break;
				case PGoNetOptions.StateOptions.STATE_SERVER:
					break;
				default:
					throw new Unreachable();
			}
			throw new TODO();
		}
		processes.accept(new PlusCalProcessesCodeGenVisitor(
				registry, typeMap, globalVariableStrategy, algorithm, moduleBuilder));
		return moduleBuilder.getModule();
	}
}
