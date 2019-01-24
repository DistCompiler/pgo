package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLAIdentifier;
import pgo.model.tla.TLARef;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.UnsupportedFeatureIssue;
import pgo.trans.passes.codegen.NameCleaner;

import java.util.*;
import java.util.stream.Stream;

public class PlusCalCodeGenPass {
	private PlusCalCodeGenPass() {}

	private static void recordMapping(DefinitionRegistry registry, Map<UID, ModularPlusCalMapping> mappedVars,
	                                  Map<UID, ModularPlusCalMappingMacro> mappings, Set<UID> functionMappedVars,
	                                  UID uid, TLAExpression value) {
		ModularPlusCalMapping mapping = mappedVars.get(registry.followReference(value.getUID()));
		if (mapping != null) {
			if (mapping.getVariable().isFunctionCalls()){
				functionMappedVars.add(uid);
			}
			mappings.put(uid, registry.findMappingMacro(mapping.getTarget().getName()));
		}
	}

	public static PlusCalAlgorithm perform(IssueContext ctx, DefinitionRegistry registry,
	                                       ModularPlusCalBlock modularPlusCalBlock) {
		// separate the procedures with ref arguments and ones without
		List<PlusCalProcedure> procedures = new ArrayList<>();
		Map<UID, PlusCalProcedure> refProcedures = new HashMap<>();
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			if (procedure.getParams().stream().anyMatch(PlusCalVariableDeclaration::isRef)) {
				refProcedures.put(procedure.getUID(), procedure);
			} else {
				procedures.add(procedure);
			}
		}

		// seed for the name cleaner
		Set<String> nameCleanerSeed = new HashSet<>();
		PlusCalStatementNameCollectorVisitor nameCollector = new PlusCalStatementNameCollectorVisitor(nameCleanerSeed);
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			nameCleanerSeed.add(procedure.getName());
			Stream.concat(procedure.getVariables().stream(), procedure.getParams().stream())
					.forEach(v -> nameCleanerSeed.add(v.getName().getValue()));
			procedure.getBody().forEach(s -> s.accept(nameCollector));
		}
		if (modularPlusCalBlock.getProcesses() instanceof PlusCalMultiProcess) {
			for (PlusCalProcess process : ((PlusCalMultiProcess) modularPlusCalBlock.getProcesses()).getProcesses()) {
				nameCleanerSeed.add(process.getName().getName().getValue());
				for (PlusCalVariableDeclaration declaration : process.getVariables()) {
					nameCleanerSeed.add(declaration.getName().getValue());
				}
				process.getBody().forEach(s -> s.accept(nameCollector));
			}
		}
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			nameCleanerSeed.add(archetype.getName());
			Stream.concat(archetype.getParams().stream(), archetype.getParams().stream())
					.forEach(v -> nameCleanerSeed.add(v.getName().getValue()));
			archetype.getBody().forEach(s -> s.accept(nameCollector));
		}
		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			nameCleanerSeed.add(mappingMacro.getName());
			mappingMacro.getReadBody().forEach(s -> s.accept(nameCollector));
			mappingMacro.getWriteBody().forEach(s -> s.accept(nameCollector));
		}
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			nameCleanerSeed.add(instance.getName().getName().getValue());
		}
		NameCleaner nameCleaner = new NameCleaner(nameCleanerSeed);

		// expand the instances
		List<PlusCalProcess> processList = new ArrayList<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Map<UID, ModularPlusCalMapping> mappedVars = new HashMap<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				mappedVars.put(registry.followReference(mapping.getVariable().getUID()), mapping);
			}
			ModularPlusCalArchetype archetype = registry.findArchetype(instance.getTarget());
			Map<UID, PlusCalVariableDeclaration> params = new HashMap<>();
			Map<UID, TLAGeneralIdentifier> arguments = new LinkedHashMap<>();
			Map<UID, ModularPlusCalMappingMacro> mappings = new HashMap<>();
			Set<UID> functionMappedVars = new HashSet<>();
			Set<UID> refs = new HashSet<>();
			List<PlusCalVariableDeclaration> localVariables = new ArrayList<>(archetype.getVariables());
			TemporaryBinding readTemporaryBinding = new TemporaryBinding(nameCleaner, localVariables);
			for (int i = 0; i < archetype.getParams().size(); i++) {
				PlusCalVariableDeclaration argument = archetype.getParams().get(i);
				UID uid = argument.getUID();
				TLAExpression value = instance.getArguments().get(i);
				params.put(uid, argument);
				if (value instanceof TLARef) {
					recordMapping(registry, mappedVars, mappings, functionMappedVars, uid, value);
					refs.add(uid);
					arguments.put(
							uid,
							new TLAGeneralIdentifier(
									value.getLocation(),
									new TLAIdentifier(
											value.getLocation(),
											((TLARef) value).getTarget()),
									Collections.emptyList()));
				} else if (value instanceof TLAGeneralIdentifier) {
					recordMapping(registry, mappedVars, mappings, functionMappedVars, uid, value);
					arguments.put(uid, (TLAGeneralIdentifier) value);
				} else {
					// this argument is bound to a TLA+ expression, so we need to add a variable declaration for it
					readTemporaryBinding.declare(
							value.getLocation(), uid, argument.getName().getValue() + "Read", value);
				}
			}
			ModularPlusCalCodeGenVisitor v = new ModularPlusCalCodeGenVisitor(
					registry, params, arguments, mappings, refs, functionMappedVars, readTemporaryBinding,
					new TemporaryBinding(nameCleaner, localVariables));
			List<PlusCalStatement> body = new ArrayList<>();
			for (PlusCalStatement statement : archetype.getBody()) {
				body.addAll(statement.accept(v));
			}
			processList.add(new PlusCalProcess(
					instance.getLocation(),
					instance.getName(),
					instance.getFairness(),
					localVariables,
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
				procedures,
				modularPlusCalBlock.getUnits(),
				processes);
	}
}
