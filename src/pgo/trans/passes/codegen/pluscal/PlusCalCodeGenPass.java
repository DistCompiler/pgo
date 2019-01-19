package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.tla.TLAIdentifier;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.UnsupportedFeatureIssue;
import pgo.trans.passes.atomicity.PlusCalStatementAtomicityInferenceVisitor;

import java.util.*;
import java.util.stream.Stream;

public class PlusCalCodeGenPass {
	private PlusCalCodeGenPass() {}

	private static <T> void trackArgumentAccess(DefinitionRegistry registry, Map<UID, T> arguments,
	                                            Map<UID, Set<UID>> tracker, UID varUID, UID labelUID) {
		UID uid = registry.followReference(varUID);
		if (arguments.containsKey(uid)) {
			if (tracker.containsKey(labelUID)) {
				tracker.get(labelUID).add(uid);
			} else {
				Set<UID> uids = new LinkedHashSet<>();
				uids.add(uid);
				tracker.put(labelUID, uids);
			}
		}
	}

	public static PlusCalAlgorithm perform(IssueContext ctx, DefinitionRegistry registry,
	                                       ModularPlusCalBlock modularPlusCalBlock) {
		Set<String> nameCleanerSeed = new HashSet<>();
		PlusCalStatementNameCollectorVisitor nameCollector = new PlusCalStatementNameCollectorVisitor(nameCleanerSeed);
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			nameCleanerSeed.add(procedure.getName());
			Stream.concat(procedure.getVariables().stream(), procedure.getArguments().stream())
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
			Stream.concat(archetype.getArguments().stream(), archetype.getArguments().stream())
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
		List<PlusCalProcess> processList = new ArrayList<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Map<UID, ModularPlusCalMapping> mappedVars = new HashMap<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				mappedVars.put(registry.followReference(mapping.getVariable().getUID()), mapping);
			}
			ModularPlusCalArchetype archetype = registry.findArchetype(instance.getTarget());
			Map<UID, PlusCalVariableDeclaration> arguments = new HashMap<>();
			Map<UID, TLAGeneralIdentifier> params = new HashMap<>();
			Map<UID, ModularPlusCalMappingMacro> mappings = new HashMap<>();
			Set<UID> functionMappedVars = new HashSet<>();
			Set<UID> refs = new HashSet<>();
			List<PlusCalVariableDeclaration> localVariables = new ArrayList<>(archetype.getVariables());
			TemporaryBinding readTemporaryBinding = new TemporaryBinding(nameCleaner, localVariables);
			for (int i = 0; i < archetype.getArguments().size(); i++) {
				PlusCalVariableDeclaration argument = archetype.getArguments().get(i);
				UID uid = argument.getUID();
				TLAExpression value = instance.getParams().get(i);
				arguments.put(uid, argument);
				if (value instanceof TLARef) {
					recordMapping(registry, mappedVars, mappings, functionMappedVars, uid, value);
					refs.add(uid);
					params.put(
							uid,
							new TLAGeneralIdentifier(
									value.getLocation(),
									new TLAIdentifier(
											value.getLocation(),
											((TLARef) value).getTarget()),
									Collections.emptyList()));
				} else if (value instanceof TLAGeneralIdentifier) {
					recordMapping(registry, mappedVars, mappings, functionMappedVars, uid, value);
					params.put(uid, (TLAGeneralIdentifier) value);
				} else {
					// this argument is bound to a TLA+ expression, so we need to add a variable declaration for it
					readTemporaryBinding.declare(
							value.getLocation(), uid, argument.getName().getValue() + "Read", value);
				}
			}
			// discover argument reads
			Map<UID, Set<UID>> labelsToVarReads = new HashMap<>();
			// discover argument writes
			Map<UID, Set<UID>> labelsToVarWrites = new HashMap<>();
			PlusCalStatementAtomicityInferenceVisitor visitor = new PlusCalStatementAtomicityInferenceVisitor(
					new UID(),
					(varUID, labelUID) -> trackArgumentAccess(registry, params, labelsToVarReads, varUID, labelUID),
					(varUID, labelUID) -> trackArgumentAccess(registry, params, labelsToVarWrites, varUID, labelUID),
					new HashSet<>());
			for (PlusCalStatement statement : archetype.getBody()) {
				statement.accept(visitor);
			}
			ModularPlusCalCodeGenVisitor v = new ModularPlusCalCodeGenVisitor(
					registry, labelsToVarReads, labelsToVarWrites, arguments, params, mappings, refs,
					functionMappedVars, readTemporaryBinding, new TemporaryBinding(nameCleaner, localVariables));
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
				modularPlusCalBlock.getProcedures(),
				modularPlusCalBlock.getUnits(),
				processes);
	}

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
}
