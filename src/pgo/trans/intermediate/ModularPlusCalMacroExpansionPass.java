package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;

import java.util.*;

public class ModularPlusCalMacroExpansionPass {
	
	private ModularPlusCalMacroExpansionPass() {}
	
	public static ModularPlusCalBlock perform(IssueContext ctx, ModularPlusCalBlock modularPlusCalBlock) {
		Map<String, PlusCalMacro> macros = new HashMap<>();
		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			if(macros.containsKey(macro.getName())) {
				ctx.error(new MacroNameConflictIssue(macros.get(macro.getName()), macro));
			}else {
				macros.put(macro.getName(), macro);
			}
		}

		List<PlusCalProcedure> procedures = new ArrayList<>();
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		modularPlusCalBlock.getProcedures().forEach(proc -> {
			List<PlusCalStatement> stmts = new ArrayList<>();
			for (PlusCalStatement stmt : proc.getBody()) {
				stmts.addAll(stmt.accept(v));
			}

			procedures.add(new PlusCalProcedure(
					proc.getLocation(),
					proc.getName(),
					proc.getArguments(),
					proc.getVariables(),
					stmts));
		});

		return new ModularPlusCalBlock(
				modularPlusCalBlock.getLocation(),
				modularPlusCalBlock.getName(),
				modularPlusCalBlock.getVariables(),
				modularPlusCalBlock.getUnits(),
				Collections.emptyList(),
				Collections.emptyList(),
				Collections.emptyList(),
				procedures,
				Collections.emptyList(),
				modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}

}
