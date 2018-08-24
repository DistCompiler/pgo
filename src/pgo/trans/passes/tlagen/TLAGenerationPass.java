package pgo.trans.passes.tlagen;

import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAUnit;
import pgo.model.tla.builder.TLAModuleBuilder;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.NameCleaner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Compiles a PlusCal algorithm into TLA+ that can be checked by the TLC
 */
public final class TLAGenerationPass {

	public static List<TLAUnit> perform(DefinitionRegistry definitionRegistry, PlusCalAlgorithm algorithm) {

		TLAModuleBuilder moduleBuilder = new TLAModuleBuilder();

		NameCleaner nameCleaner = moduleBuilder.getNameCleaner();

		List<UID> allVariables = new ArrayList<>();
		Map<UID, String> renamingMap = new HashMap<>();
		for(PlusCalVariableDeclaration decl : algorithm.getVariables()) {
			allVariables.add(decl.getUID());
			renamingMap.put(decl.getUID(), nameCleaner.cleanName(decl.getName().getValue()));
		}

		// TODO: that's not all the variables

		algorithm.getProcesses().accept(new PlusCalProcessesTranslationVisitor(
				definitionRegistry, moduleBuilder, allVariables, renamingMap));

		return moduleBuilder.getUnits();
	}

}
