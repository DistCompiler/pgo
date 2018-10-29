package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.golang.NameCleaner;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.UnsupportedFeatureIssue;

import java.util.*;
import java.util.stream.Stream;

public class PlusCalCodeGenPass {
	private PlusCalCodeGenPass() {}

	public static PlusCalAlgorithm perform(IssueContext ctx, DefinitionRegistry registry,
										   ModularPlusCalBlock modularPlusCalBlock) {
		// TODO seed with variable declaration in with and let statements
		Set<String> nameCleanerSeed = new HashSet<>();
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			nameCleanerSeed.add(procedure.getName());
			Stream.concat(procedure.getVariables().stream(), procedure.getArguments().stream())
					.forEach(v -> nameCleanerSeed.add(v.getName().getValue()));
		}
		if (modularPlusCalBlock.getProcesses() instanceof PlusCalMultiProcess) {
			for (PlusCalProcess process : ((PlusCalMultiProcess) modularPlusCalBlock.getProcesses()).getProcesses()) {
				nameCleanerSeed.add(process.getName().getName().getValue());
				for (PlusCalVariableDeclaration declaration : process.getVariables()) {
					nameCleanerSeed.add(declaration.getName().getValue());
				}
			}
		}
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
            nameCleanerSeed.add(archetype.getName());
            Stream.concat(archetype.getArguments().stream(), archetype.getArguments().stream())
		            .forEach(v -> nameCleanerSeed.add(v.getName().getValue()));
		}
		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
            nameCleanerSeed.add(mappingMacro.getName());
		}
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			nameCleanerSeed.add(instance.getName().getName().getValue());
		}
		NameCleaner nameCleaner = new NameCleaner(nameCleanerSeed);
		List<PlusCalProcess> processList = new ArrayList<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Map<UID, ModularPlusCalMappingMacro> mappings = new HashMap<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				mappings.put(
						registry.followReference(mapping.getVariable().getUID()),
						registry.findMappingMacro(mapping.getTarget().getName()));
			}
			ModularPlusCalArchetype archetype = registry.findArchetype(instance.getTarget());
			Map<UID, PlusCalVariableDeclaration> arguments = new HashMap<>();
			Map<UID, TLAExpression> boundValues = new HashMap<>();
			List<PlusCalVariableDeclaration> variables = new ArrayList<>(archetype.getVariables());
			for (int i = 0; i < archetype.getArguments().size(); i++) {
				PlusCalVariableDeclaration argument = archetype.getArguments().get(i);
				UID uid = argument.getUID();
				TLAExpression value = instance.getParams().get(i);
				arguments.put(uid, argument);
				boundValues.put(uid, value);
				if (!(value instanceof TLARef) && !(value instanceof TLAGeneralIdentifier)) {
					// this argument is bound to a TLA+ expression, so we need to add a variable declaration for it
					// TODO renaming
					variables.add(new PlusCalVariableDeclaration(
							value.getLocation(), argument.getName(), false, false, value));
				}
			}
			List<PlusCalStatement> body = new ArrayList<>();
			ModularPlusCalMappingMacroExpansionVisitor v = new ModularPlusCalMappingMacroExpansionVisitor(
					registry, nameCleaner, arguments, boundValues, variables, mappings);
			for (PlusCalStatement statement : archetype.getBody()) {
				body.addAll(statement.accept(v));
			}
			processList.add(new PlusCalProcess(
					instance.getLocation(),
					instance.getName(),
					instance.getFairness(),
					variables,
					body));
		}
		PlusCalProcesses processes = modularPlusCalBlock.getProcesses();
		if (processes instanceof PlusCalSingleProcess && processList.size() != 0) {
			ctx.error(new UnsupportedFeatureIssue("single process with instances"));
		} else if (processes instanceof PlusCalMultiProcess) {
			processList.addAll(((PlusCalMultiProcess) processes).getProcesses());
			processes = new PlusCalMultiProcess(processes.getLocation(), processList);
		} else {
			throw new Unreachable();
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
