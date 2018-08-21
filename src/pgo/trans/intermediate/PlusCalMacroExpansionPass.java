package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalMacro;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public class PlusCalMacroExpansionPass {
	
	private PlusCalMacroExpansionPass() {}
	
	public static PlusCalAlgorithm perform(IssueContext ctx, PlusCalAlgorithm plusCalAlgorithm) {
		Map<String, PlusCalMacro> macros = new HashMap<>();
		for(PlusCalMacro macro : plusCalAlgorithm.getMacros()) {
			if(macros.containsKey(macro.getName())) {
				ctx.error(new MacroNameConflictIssue(macros.get(macro.getName()), macro));
			}else {
				macros.put(macro.getName(), macro);
			}
		}
		return new PlusCalAlgorithm(
				plusCalAlgorithm.getLocation(),
				plusCalAlgorithm.getFairness(),
				plusCalAlgorithm.getName(),
				plusCalAlgorithm.getVariables(),
				Collections.emptyList(),
				plusCalAlgorithm.getProcedures(),
				plusCalAlgorithm.getUnits(),
				plusCalAlgorithm.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}

}
