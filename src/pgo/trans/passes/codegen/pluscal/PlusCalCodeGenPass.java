package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.*;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.UnsupportedFeatureIssue;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.trans.passes.validation.NonModularPlusCalNodeValidationVisitor;

import java.util.*;
import java.util.stream.Stream;

public class PlusCalCodeGenPass {
	private PlusCalCodeGenPass() {}

	private static void recordMapping(DefinitionRegistry registry, Map<UID, ModularPlusCalMapping> mappedVars,
	                                  UID paramUID, UID mappedUID, Map<UID, ModularPlusCalMappingMacro> mappings,
	                                  Set<UID> functionMappedVars) {
		ModularPlusCalMapping mapping = mappedVars.get(mappedUID);
		if (mapping != null) {
			if (mapping.getVariable().isFunctionCall()){
				functionMappedVars.add(paramUID);
			}
			mappings.put(paramUID, registry.findMappingMacro(mapping.getTarget().getName()));
		}
	}

	public static PlusCalAlgorithm perform(IssueContext ctx, DefinitionRegistry registry,
	                                       ModularPlusCalBlock modularPlusCalBlock) {
		// separate the procedures with ref arguments and ones without
		List<PlusCalProcedure> procedures = new ArrayList<>();
		NonModularPlusCalNodeValidationVisitor nonModularPlusCalNodeValidationVisitor =
				new NonModularPlusCalNodeValidationVisitor();
		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			if (procedure.accept(nonModularPlusCalNodeValidationVisitor)) {
				procedures.add(procedure);
			}
		}
		Map<ExpandedProcedureMatch, String> procedureCache = new HashMap<>();

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
		List<PlusCalVariableDeclaration> globalVariables = new ArrayList<>(modularPlusCalBlock.getVariables());
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
			Set<UID> expressionArguments = new HashSet<>();
			Set<UID> functionMappedVars = new HashSet<>();
			Set<UID> refs = new HashSet<>();
			List<PlusCalVariableDeclaration> localVariables = new ArrayList<>();
			TemporaryBinding readTemporaryBinding = new TemporaryBinding(nameCleaner, globalVariables);
			List<PlusCalVariableDeclaration> archetypeParams = archetype.getParams();
			List<TLAExpression> instanceArguments = instance.getArguments();
			// initialization statements for parameters bound to expressions
			List<PlusCalStatement> initStatements = new ArrayList<>();
			for (int i = 0; i < archetypeParams.size(); i++) {
				PlusCalVariableDeclaration param = archetypeParams.get(i);
				UID paramUID = param.getUID();
				TLAExpression value = instanceArguments.get(i);
				params.put(paramUID, param);
				if (value instanceof TLARef) {
					recordMapping(
							registry, mappedVars, paramUID, registry.followReference(value.getUID()), mappings,
							functionMappedVars);
					refs.add(paramUID);
					arguments.put(
							paramUID,
							new TLAGeneralIdentifier(
									value.getLocation(),
									new TLAIdentifier(
											value.getLocation(),
											((TLARef) value).getTarget()),
									Collections.emptyList()));
				} else if (value instanceof TLAGeneralIdentifier) {
					recordMapping(
							registry, mappedVars, paramUID, registry.followReference(value.getUID()), mappings,
							functionMappedVars);
					arguments.put(paramUID, (TLAGeneralIdentifier) value);
				} else {
					recordMapping(registry, mappedVars, paramUID, paramUID, mappings, functionMappedVars);
					if (param.isRef()) {
						refs.add(paramUID);
					}
					String nameHint = param.getName().getValue() + "Local";
					// this argument is bound to a TLA+ expression, so we need to add a variable declaration for it
					TLAGeneralIdentifier local;
					if (value.accept(
							new TLAExpressionParamsAccessCheckVisitor(registry, params, Collections.emptyMap()))) {
						local = readTemporaryBinding.freshVariable(value.getLocation(), paramUID, nameHint);
						localVariables.add(new PlusCalVariableDeclaration(
								value.getLocation(),
								new Located<>(value.getLocation(), local.getName().getId()),
								false,
								false,
								new PlusCalDefaultInitValue(value.getLocation())));
						TLAGeneralIdentifier lhs = new TLAGeneralIdentifier(
								param.getLocation(),
								new TLAIdentifier(param.getLocation(), local.getName().getId()),
								Collections.emptyList());
						initStatements.add(new PlusCalAssignment(
								value.getLocation(),
								Collections.singletonList(new PlusCalAssignmentPair(value.getLocation(),lhs, value))));
					} else {
						local = readTemporaryBinding.freshVariable(value.getLocation(), paramUID, nameHint);
						localVariables.add(new PlusCalVariableDeclaration(
								value.getLocation(), new Located<>(value.getLocation(), local.getName().getId()),
								false, false, value));
					}
					arguments.put(paramUID, local);
					readTemporaryBinding.reuse(paramUID);
					expressionArguments.add(paramUID);
				}
			}
			TemporaryBinding writeTemporaryBinding = new TemporaryBinding(nameCleaner, globalVariables);
			ProcedureExpander procedureExpander = new ProcedureExpander(
					ctx, registry, nameCleaner, procedureCache, arguments, mappings, refs, functionMappedVars,
					procedures);
			// initialize the local variables
			ModularPlusCalCodeGenVisitor v = new ModularPlusCalCodeGenVisitor(
					registry, params, arguments, mappings, expressionArguments, functionMappedVars,
					readTemporaryBinding, writeTemporaryBinding, procedureExpander,
					new TLAExpressionPlusCalCodeGenVisitor(registry, params, arguments, expressionArguments, mappings,
							functionMappedVars, readTemporaryBinding, writeTemporaryBinding, procedureExpander,
							Collections.emptyList()));
			List<PlusCalStatement> body = new ArrayList<>();
			ProcedureExpander.initializeLocalVariables(
					registry, archetype.getLocation(), params, archetype.getVariables(),
					nameCleaner.cleanName("init"), v, localVariables, initStatements, body);
			for (PlusCalStatement statement : archetype.getBody()) {
				body.addAll(statement.accept(v));
			}
			processList.add(new PlusCalProcess(
					instance.getLocation(), instance.getName(), instance.getFairness(), localVariables, body));
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
				globalVariables,
				Collections.emptyList(),
				procedures,
				modularPlusCalBlock.getUnits(),
				processes);
	}
}
