package pgo.trans.passes.expansion;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;

import java.util.*;

public class ModularPlusCalMacroExpansionPass {
	private ModularPlusCalMacroExpansionPass() {}

	public static ModularPlusCalBlock perform(IssueContext ctx, ModularPlusCalBlock modularPlusCalBlock) {
		Map<String, PlusCalMacro> macros = new HashMap<>();
		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			if (macros.containsKey(macro.getName())) {
				ctx.error(new MacroNameConflictIssue(macros.get(macro.getName()), macro));
				continue;
			}
			macros.put(macro.getName(), macro);
		}

		List<PlusCalProcedure> procedures = new ArrayList<>();
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		for (PlusCalProcedure proc : modularPlusCalBlock.getProcedures()) {
			List<PlusCalStatement> stmts = new ArrayList<>();
			for (PlusCalStatement stmt : proc.getBody()) {
				stmts.addAll(stmt.accept(v));
			}

			procedures.add(new PlusCalProcedure(
					proc.getLocation(),
					proc.getName(),
					proc.getParams(),
					proc.getVariables(),
					stmts));
		}

		return new ModularPlusCalBlock(
				modularPlusCalBlock.getLocation(),
				modularPlusCalBlock.getName(),
				modularPlusCalBlock.getVariables(),
				modularPlusCalBlock.getUnits(),
				modularPlusCalBlock.getMappingMacros(),
				modularPlusCalBlock.getArchetypes(),
				Collections.emptyList(),
				procedures,
				modularPlusCalBlock.getInstances(),
				modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}
}
