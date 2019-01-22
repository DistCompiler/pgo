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

	private static List<PlusCalStatement> desugarLabeledStatements(List<PlusCalStatement> labeledStatements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : labeledStatements) {
			PlusCalLabeledStatements lblStmts = (PlusCalLabeledStatements) statement;
			ModularPlusCalDesugarVisitor visitor = new ModularPlusCalDesugarVisitor(lblStmts.getLabel());
			List<PlusCalStatement> stmts = new ArrayList<>();
			for (PlusCalStatement stmt : lblStmts.getStatements()) {
				stmts.addAll(stmt.accept(visitor));
			}
			result.add(new PlusCalLabeledStatements(lblStmts.getLocation(), lblStmts.getLabel(), stmts));
		}
		return result;
	}

	public static ModularPlusCalBlock perform(ModularPlusCalBlock modularPlusCalBlock) {
		List<ModularPlusCalArchetype> archetypes = new ArrayList<>();
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            archetypes.add(new ModularPlusCalArchetype(
            		archetype.getLocation(),
		            archetype.getName(),
		            archetype.getArguments(),
		            archetype.getVariables(),
		            desugarLabeledStatements(archetype.getBody())));
		}
		List<PlusCalProcedure> procedures = new ArrayList<>();
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			procedures.add(new PlusCalProcedure(
					procedure.getLocation(),
					procedure.getName(),
					procedure.getArguments(),
					procedure.getVariables(),
					desugarLabeledStatements(procedure.getBody())));
		}
		return new ModularPlusCalBlock(
				modularPlusCalBlock.getLocation(),
				modularPlusCalBlock.getName(),
				modularPlusCalBlock.getVariables(),
				modularPlusCalBlock.getUnits(),
				modularPlusCalBlock.getMappingMacros(),
				archetypes,
				Collections.emptyList(),
				procedures,
				modularPlusCalBlock.getInstances(),
				modularPlusCalBlock.getProcesses());
	}
}
