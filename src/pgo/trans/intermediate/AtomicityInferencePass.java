package pgo.trans.intermediate;

import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.Procedure;
import pgo.scope.UID;

public class AtomicityInferencePass {
	private AtomicityInferencePass() {}

	private static void addGlobalVarRead(DefinitionRegistry registry, UID labelUID, UID varUID) {
		if (registry.isGlobalVariable(varUID)) {
			registry.addGlobalVarRead(labelUID, varUID);
		}
	}

	private static void addGlobalVarWrite(DefinitionRegistry registry, UID labelUID, UID varUID) {
		if (registry.isGlobalVariable(varUID)) {
			registry.addGlobalVarWrite(labelUID, varUID);
		}
	}

	public static void perform(DefinitionRegistry registry, Algorithm pcalAlgorithm) {
		if (pcalAlgorithm.getProcesses() instanceof MultiProcess) {
			for (Procedure p : pcalAlgorithm.getProcedures()) {
				for (LabeledStatements statements : p.getBody()) {
					UID labelUID = statements.getLabel().getUID();
					registry.addLabel(p.getUID(), labelUID);
					statements.accept(new PlusCalStatementAtomicityInferenceVisitor(
							varUID -> addGlobalVarRead(registry, labelUID, varUID),
							varUID -> addGlobalVarWrite(registry, labelUID, varUID)));
				}
			}

			pcalAlgorithm.getProcesses().accept(new PlusCalProcessesAtomicityInferenceVisitor(
					registry::addLabel,
					labelUID -> varUID -> addGlobalVarRead(registry, labelUID, varUID),
					labelUID -> varUID -> addGlobalVarWrite(registry, labelUID, varUID)));
		}
	}
}
