package pgo.trans.intermediate;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.Macro;

public class PlusCalMacroExpansionPass {
	
	private PlusCalMacroExpansionPass() {}
	
	public static Algorithm perform(IssueContext ctx, Algorithm algorithm) {
		Map<String, Macro> macros = new HashMap<>();
		for(Macro macro : algorithm.getMacros()) {
			if(macros.containsKey(macro.getName())) {
				ctx.error(new MacroNameConflictIssue(macros.get(macro.getName()), macro));
			}else {
				macros.put(macro.getName(), macro);
			}
		}
		return new Algorithm(
				algorithm.getLocation(),
				algorithm.getName(),
				algorithm.getVariables(),
				Collections.emptyList(),
				algorithm.getProcedures(),
				algorithm.getUnits(),
				algorithm.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}

}
