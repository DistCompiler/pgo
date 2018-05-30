package pgo.trans.intermediate;

import java.util.Map;

import pgo.PGoOptions;
import pgo.model.golang.Module;
import pgo.model.golang.ModuleBuilder;
import pgo.model.pcal.Algorithm;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class CodeGenPass {

	private CodeGenPass() {}

	public static Module perform(Algorithm algorithm, DefinitionRegistry registry, Map<UID, PGoType> typeMap, PGoOptions opts) {
		ModuleBuilder moduleBuilder = new ModuleBuilder(algorithm.getName());

		GlobalVariableStrategy globalStrategy = new SingleFunctionGlobalVariableStrategy(algorithm, registry, typeMap);

		algorithm.getProcesses().accept(
				new PlusCalProcessesSingleThreadedCodeGenVisitor(moduleBuilder, registry, typeMap, globalStrategy));

		return moduleBuilder.getModule();
	}

}
