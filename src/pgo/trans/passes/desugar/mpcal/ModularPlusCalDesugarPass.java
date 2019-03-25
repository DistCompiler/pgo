package pgo.trans.passes.desugar.mpcal;

import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalLabeledStatements;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ModularPlusCalDesugarPass {
	private ModularPlusCalDesugarPass() {}

	private static List<PlusCalStatement> desugarLabeledStatements(ModularPlusCalDesugarVisitor visitor,
	                                                               List<PlusCalStatement> labeledStatements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : labeledStatements) {
			PlusCalLabeledStatements lblStmts = (PlusCalLabeledStatements) statement;
			result.addAll(lblStmts.accept(visitor));
		}
		return result;
	}

	public static ModularPlusCalBlock perform(ModularPlusCalBlock modularPlusCalBlock) {
		ModularPlusCalDesugarVisitor visitor = new ModularPlusCalDesugarVisitor();
		List<ModularPlusCalArchetype> archetypes = new ArrayList<>();
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			archetypes.add(new ModularPlusCalArchetype(
					archetype.getLocation(),
					archetype.getName(),
					archetype.getParams(),
					archetype.getVariables(),
					desugarLabeledStatements(visitor, archetype.getBody())));
		}
		List<PlusCalProcedure> procedures = new ArrayList<>();
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			procedures.add(new PlusCalProcedure(
					procedure.getLocation(),
					procedure.getName(),
					procedure.getParams(),
					procedure.getVariables(),
					desugarLabeledStatements(visitor, procedure.getBody())));
		}
		return new ModularPlusCalBlock(
				modularPlusCalBlock.getLocation(),
				modularPlusCalBlock.getName(),
				modularPlusCalBlock.getUnits(),
				Collections.emptyList(),
				procedures,
				modularPlusCalBlock.getMappingMacros(),
				archetypes,
				modularPlusCalBlock.getVariables(),
				modularPlusCalBlock.getInstances(),
				modularPlusCalBlock.getProcesses());
	}
}
