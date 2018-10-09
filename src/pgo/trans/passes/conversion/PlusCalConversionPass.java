package pgo.trans.passes.conversion;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.trans.intermediate.UnsupportedFeatureIssue;
import pgo.trans.passes.expansion.ModularPlusCalMappingMacroExpansionVisitor;

import java.util.*;

public class PlusCalConversionPass {
	private PlusCalConversionPass() {}

	public static PlusCalAlgorithm perform(IssueContext ctx, ModularPlusCalBlock modularPlusCalBlock) {
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
				String name = mapping.getVariable().getName();
				if (mappings.containsKey(name)) {
					mappings.get(name).add(mapping.getTarget().getName());
				} else {
					List<String> l = new ArrayList<>();
					l.add(mapping.getTarget().getName());
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
		return new PlusCalAlgorithm(
				modularPlusCalBlock.getLocation(),
				PlusCalFairness.UNFAIR,
				modularPlusCalBlock.getName(),
				modularPlusCalBlock.getVariables(),
				Collections.emptyList(),
				modularPlusCalBlock.getProcedures(),
				modularPlusCalBlock.getUnits(),
				processes);
	}
}
