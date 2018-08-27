package pgo.trans.intermediate;

import pgo.errors.IssueContext;
import pgo.model.pcal.PlusCalAlgorithm;
import pgo.model.pcal.PlusCalMacro;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;

import java.util.*;

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

		List<PlusCalProcedure> procedures = new ArrayList<>();
		PlusCalMacroExpansionVisitor v = new PlusCalMacroExpansionVisitor(ctx, macros, new HashSet<>(), new HashMap<>());
		plusCalAlgorithm.getProcedures().forEach(proc -> {
			List<PlusCalStatement> stmts = new ArrayList<>();
			for (PlusCalStatement stmt : proc.getBody()) {
				for (PlusCalStatement s : stmt.accept(v)) {
					stmts.add(s);
				}
			}

			procedures.add(new PlusCalProcedure(
					proc.getLocation(),
					proc.getName(),
					proc.getArguments(),
					proc.getVariables(),
					stmts));
		});

		return new PlusCalAlgorithm(
				plusCalAlgorithm.getLocation(),
				plusCalAlgorithm.getFairness(),
				plusCalAlgorithm.getName(),
				plusCalAlgorithm.getVariables(),
				Collections.emptyList(),
				procedures,
				plusCalAlgorithm.getUnits(),
				plusCalAlgorithm.getProcesses().accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}

}
