package pgo.trans.passes.validation;

import java.util.*;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.model.tla.TLAUnit;
import pgo.scope.UID;

import java.util.function.Consumer;

/**
 * Validates that the Modular PlusCal specification is valid according to the restrictions
 * imposed by the language (documented at https://github.com/UBC-NSS/pgo/wiki/Modular-PlusCal).
 */
public class ModularPlusCalValidationVisitor extends ModularPlusCalBlockVisitor<Void, RuntimeException> {
	private final IssueContext ctx;
	private final Map<UID, Map<String, Boolean>> archetypeFunctionMappings;

	public ModularPlusCalValidationVisitor(IssueContext ctx) {
		this.ctx = ctx;
		this.archetypeFunctionMappings = new HashMap<>();
	}

	// validates that instances of an archetype cannot instantiate the same global variable
	// in inconsistent ways: i.e., one mapping function calls and the other mapping the variable
	// itself (or not applying any mapping to it).
	private void validateConsistentInstantiations(ModularPlusCalBlock modularPlusCalBlock) {
		Map<String, List<ModularPlusCalInstance>> instanceMap = new HashMap<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			List<ModularPlusCalInstance> existingInstances = instanceMap.getOrDefault(instance.getTarget(), new ArrayList<>());

			if (existingInstances.size() > 0) {
				for (ModularPlusCalInstance existingInstance : existingInstances) {
					Set<ModularPlusCalMapping> existingMappingsUnique = new HashSet<>(existingInstance.getMappings());
					Set<ModularPlusCalMapping> currentMappingsUnique = new HashSet<>(instance.getMappings());


					for (ModularPlusCalMapping existingMapping : existingInstance.getMappings()) {
						for (ModularPlusCalMapping currentMapping : instance.getMappings()) {
							if (existingMapping.getVariable().getName().equals(currentMapping.getVariable().getName())) {
								existingMappingsUnique.remove(existingMapping);
								currentMappingsUnique.remove(currentMapping);

								if (existingMapping.getVariable().isFunctionCalls() != currentMapping.getVariable().isFunctionCalls()) {
									ctx.error(new InconsistentInstantiationIssue(instance, existingInstance));
								}
							}
						}
					}

					// if mappings that do not match map function calls, then the instantiations
					// are conflicting.
					for (ModularPlusCalMapping mapping : existingMappingsUnique) {
						if (mapping.getVariable().isFunctionCalls()) {
							ctx.error(new InconsistentInstantiationIssue(instance, existingInstance));
						}
					}

					for (ModularPlusCalMapping mapping : currentMappingsUnique) {
						if (mapping.getVariable().isFunctionCalls()) {
							ctx.error(new InconsistentInstantiationIssue(instance, existingInstance));
						}
					}
				}
			}

			existingInstances.add(instance);
			instanceMap.put(instance.getTarget(), existingInstances);
		}
	}

	private void checkMappedParams(ModularPlusCalBlock modularPlusCalBlock) {
		modularPlusCalBlock.getArchetypes().forEach(archetype -> {
			Map<String, Boolean> functionMapped = new HashMap<>();
			Map<String, Integer> concreteToPosition = new HashMap<>();
			archetypeFunctionMappings.put(archetype.getUID(), functionMapped);

			modularPlusCalBlock
					.getInstances()
					.stream()
					.filter(i -> i.getTarget().equals(archetype.getName()))
					.findFirst()
					.ifPresent(instance -> {
						// since we already established the instances are consistent at
						// this point, it is sufficient to inspect only one instance of an
						// archetype to determine which parameters are function mapped.


						// find how each concrete argument passed to the archetype instantiation
						// maps to the positions of the arguments of the archetype.
						for (int i = 0; i < archetype.getParams().size(); i++) {
							TLAExpression arg = instance.getArguments().get(i);
							String concreteName;

							if (arg instanceof TLAGeneralIdentifier) {
								concreteName = ((TLAGeneralIdentifier) arg).getName().getId();
							} else if (arg instanceof TLARef) {
								concreteName = ((TLARef) arg).getTarget();
							} else {
								continue;
							}

							concreteToPosition.put(concreteName, i);
						}

						archetype.getParams().forEach(param -> {
							functionMapped.put(param.getName().getValue(), false);

							instance
									.getMappings()
									.stream()
									.filter(m -> m.getVariable().isFunctionCalls())
									.forEach(m -> functionMapped.put(
											archetype.getParams().get(concreteToPosition.get(m.getVariable().getName())).getName().getValue(),
											true)
									);
						});
					});
		});
	}

	public Void visit(ModularPlusCalBlock modularPlusCalBlock) {
		validateConsistentInstantiations(modularPlusCalBlock);
		checkMappedParams(modularPlusCalBlock);

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			archetype.accept(this);
		}

		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			mappingMacro.accept(this);
		}

		for (PlusCalMacro macro : modularPlusCalBlock.getMacros()) {
			macro.accept(this);
		}

		for (PlusCalProcedure procedure : modularPlusCalBlock.getProcedures()) {
			procedure.accept(this);
		}

		if (modularPlusCalBlock.getProcesses() instanceof PlusCalSingleProcess) {
			PlusCalSingleProcess singleProcess = (PlusCalSingleProcess) modularPlusCalBlock.getProcesses();
			singleProcess.accept(this);
		} else if (modularPlusCalBlock.getProcesses() instanceof PlusCalMultiProcess) {
			PlusCalMultiProcess multiProcess = (PlusCalMultiProcess) modularPlusCalBlock.getProcesses();
			multiProcess.accept(this);
		}

		return null;
	}

	/*
	* Archetypes in Modular PlusCal must obey the following rules and restrictions:
	*
	*   * Same labelling rules of vanilla PlusCal apply (see C-syntax manual, section 3.7)
	*   * Only local or `ref` variables can be assigned to
	*   * Parameters can only be used as functions if they were mapped as functions when
	*     instantiated (similarly, they cannot be used as variables if mapped as functions)
	*/
	public Void visit(ModularPlusCalArchetype modularPlusCalArchetype) {
		// guaranteed to exist at the parsing stage
		PlusCalStatement firstStatement = modularPlusCalArchetype.getBody().get(0);
		checkLabeled(firstStatement);

		Map<String, Boolean> functionMapped = archetypeFunctionMappings.get(modularPlusCalArchetype.getUID());
		ModularPlusCalLabelingRulesVisitor labels = new ModularPlusCalLabelingRulesVisitor(ctx);
		modularPlusCalArchetype.getBody().forEach(statement -> {
			statement.accept(labels);
			statement.accept(new ModularPlusCalStatementValidationVisitor(ctx, functionMapped));
		});

		return null;
	}

	public Void visit(ModularPlusCalInstance modularPlusCalInstance) {
		return null;
	}

	public Void visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) {
		// mapping macros should have no labels, `goto`, `call` or `while` statements.
		PlusCalStatementRejectionVisitor visitor = new PlusCalStatementRejectionVisitor(
				this.ctx,
				Arrays.asList(
						PlusCalStatementRejectionVisitor.Node.LABELS,
						PlusCalStatementRejectionVisitor.Node.CALL,
						PlusCalStatementRejectionVisitor.Node.GOTO,
						PlusCalStatementRejectionVisitor.Node.WHILE
				)
		);

		Consumer<List<PlusCalStatement>> validateType = statements -> {
			for (PlusCalStatement statement : statements) {
				statement.accept(visitor);
			}
		};

		validateType.accept(modularPlusCalMappingMacro.getReadBody());
		validateType.accept(modularPlusCalMappingMacro.getWriteBody());

		return null;
	}

	public Void visit(PlusCalMacro plusCalMacro) {
		ModularPlusCalLabelingRulesVisitor visitor =
				new ModularPlusCalLabelingRulesVisitor(this.ctx, false);

		// visit every statement of the macro, collecting an error in case a label
		// is found within
		for (PlusCalStatement statement : plusCalMacro.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate macros
		return null;
	}

	public Void visit(PlusCalProcedure plusCalProcedure) {
		PlusCalStatement firstStatement = plusCalProcedure.getBody().get(0);
		checkLabeled(firstStatement);

		ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
		for (PlusCalStatement statement : plusCalProcedure.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate procedures
		return null;
	}

	public Void visit(PlusCalSingleProcess plusCalSingleProcess) {
		PlusCalStatement firstStatement = plusCalSingleProcess.getBody().get(0);
		checkLabeled(firstStatement);

		ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
		for (PlusCalStatement statement : plusCalSingleProcess.getBody()) {
			statement.accept(visitor);
		}

		// TODO: validate single process
		return null;
	}

	public Void visit(PlusCalMultiProcess plusCalMultiProcess) {
		for (PlusCalProcess process : plusCalMultiProcess.getProcesses()) {
			PlusCalStatement firstStatement = process.getBody().get(0);
			checkLabeled(firstStatement);

			ModularPlusCalLabelingRulesVisitor visitor = new ModularPlusCalLabelingRulesVisitor(this.ctx);
			for (PlusCalStatement statement : process.getBody()) {
				statement.accept(visitor);
			}

			// TODO: validate PlusCal processes
		}

		return null;
	}

	public Void visit(TLAUnit tlaUnit) {
		// TODO: validate TLA+ units

		return null;
	}

	private Void checkLabeled(PlusCalStatement statement) {
		boolean isLabeled = statement instanceof PlusCalLabeledStatements;

		if (!isLabeled) {
			ctx.error(new MissingLabelIssue(statement));
		}

		return null;
	}
}