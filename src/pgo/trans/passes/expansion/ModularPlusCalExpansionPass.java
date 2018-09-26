package pgo.trans.passes.expansion;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.trans.intermediate.PlusCalMacroExpansionVisitor;
import pgo.trans.intermediate.PlusCalProcessesMacroExpansionVisitor;
import pgo.trans.intermediate.UnsupportedFeatureIssue;

import java.util.*;

public class ModularPlusCalExpansionPass {
	private ModularPlusCalExpansionPass() {}

	public static ModularPlusCalBlock perform(IssueContext ctx, ModularPlusCalBlock modularPlusCalBlock) {
		Map<String, PlusCalMacro> macros = new HashMap<>();
		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			if (macros.containsKey(macro.getName())) {
				ctx.error(new MacroNameConflictIssue(macros.get(macro.getName()), macro));
				continue;
			}
			macros.put(macro.getName(), macro);
		}

		Map<String, ModularPlusCalArchetype> archetypes = new HashMap<>();
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			archetypes.put(archetype.getName(), archetype);
		}

		Map<String, ModularPlusCalMappingMacro> mappingMacros = new HashMap<>();
		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			mappingMacros.put(mappingMacro.getName(), mappingMacro);
		}

		List<PlusCalProcess> processList = new ArrayList<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Map<String, List<String>> mappings = new HashMap<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				String name = mapping.getName().getValue();
				if (mappings.containsKey(name)) {
					mappings.get(name).add(mapping.getTarget());
				} else {
					List<String> l = new ArrayList<>();
					l.add(mapping.getTarget());
					mappings.put(name, l);
				}
			}
			ModularPlusCalArchetype archetype = archetypes.get(instance.getTarget());
			Map<String, PlusCalVariableDeclaration> arguments = new HashMap<>();
			Map<String, TLAExpression> boundArguments = new HashMap<>();
			List<PlusCalVariableDeclaration> variables = new ArrayList<>(archetype.getVariables());
			for (int i = 0; i < archetype.getArguments().size(); i++) {
				PlusCalVariableDeclaration argument = archetype.getArguments().get(i);
				String name = argument.getName().getValue();
				TLAExpression value = instance.getParams().get(i);
				arguments.put(name, argument);
				boundArguments.put(name, value);
				if (!(value instanceof TLARef) && !(value instanceof TLAGeneralIdentifier)) {
					// this argument is bound to a TLA+ expression, so we need to add a variable declaration for it
					// TODO renaming
					variables.add(new PlusCalVariableDeclaration(
							value.getLocation(), argument.getName(), false, false, value));
				}
			}
			List<PlusCalStatement> body = new ArrayList<>();
			ModularPlusCalMappingMacroExpansionVisitor v = new ModularPlusCalMappingMacroExpansionVisitor(
					ctx, arguments, boundArguments, mappingMacros, mappings);
			for (PlusCalStatement statement : archetype.getBody()) {
				body.addAll(statement.accept(v));
			}
			processList.add(new PlusCalProcess(
					instance.getLocation(),
					instance.getName(),
					PlusCalFairness.UNFAIR,
					variables,
					body));
		}
		PlusCalProcesses processes = modularPlusCalBlock.getProcesses();
		if (processes instanceof PlusCalSingleProcess && processList.size() != 0) {
			ctx.error(new UnsupportedFeatureIssue("single process with instances"));
		} else if (processes instanceof PlusCalMultiProcess) {
			processList.addAll(((PlusCalMultiProcess) processes).getProcesses());
			processes = new PlusCalMultiProcess(processes.getLocation(), processList);
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
					proc.getArguments(),
					proc.getVariables(),
					stmts));
		}

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
				processes.accept(new PlusCalProcessesMacroExpansionVisitor(ctx, macros)));
	}
}
