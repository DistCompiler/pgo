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

		// Expand macros themselves to allow macro composition
		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			PlusCalMacroExpansionVisitor macroExpander = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
			List<PlusCalStatement> stmts = new ArrayList<>();

			for (PlusCalStatement s : macro.getBody()) {
				stmts.addAll(s.accept(macroExpander));
			}

			PlusCalMacro expanded = new PlusCalMacro(macro.getLocation(), macro.getName(), macro.getParams(), stmts);
			macros.put(macro.getName(), expanded);
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

		List<ModularPlusCalArchetype> archetypes = new ArrayList<>();
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			List<PlusCalStatement> stmts = new ArrayList<>();
			for (PlusCalStatement stmt : archetype.getBody()) {
				stmts.addAll(stmt.accept(v));
			}

			archetypes.add(new ModularPlusCalArchetype(
					archetype.getLocation(),
					archetype.getId(),
					archetype.getParams(),
					archetype.getVariables(),
					stmts));
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
				modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}
}
