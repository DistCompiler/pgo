package pgo.trans.passes.validation;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.*;

public class ModularPlusCalValidationPass {
	private ModularPlusCalValidationPass() {}

	public static void perform(IssueContext ctx, ModularPlusCalBlock mpcal) {
		mpcal.accept(new ModularPlusCalValidationVisitor(ctx));
	}

	/**
	 *   * Only local or `ref` variables can be assigned to
	 *   * Parameters can only be used as functions if they were mapped as functions when
	 *     instantiated (similarly, they cannot be used as variables if mapped as functions)
	 */
	public static void performPostScoping(TopLevelIssueContext ctx, DefinitionRegistry registry,
	                                      ModularPlusCalBlock modularPlusCalBlock) {
		Map<UID, ModularPlusCalInstance> archetypesToInstance = new HashMap<>();
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Map<UID, Integer> seenVars = new HashMap<>();
			List<TLAExpression> arguments = instance.getArguments();
			for (int i = 0; i < arguments.size(); i++) {
				TLAExpression argument = arguments.get(i);
				if (argument instanceof TLAGeneralIdentifier || argument instanceof TLARef) {
					UID varUID = registry.followReference(argument.getUID());
					if (seenVars.containsKey(varUID)) {
						ctx.error(new VariableMappedMultipleTimesIssue(varUID, instance));
						continue;
					}
					// 0-indexing
					seenVars.put(varUID, i);
				}
			}
			ModularPlusCalArchetype archetype = registry.findArchetype(instance.getTarget());
			boolean[] signature = new boolean[instance.getArguments().size()];
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				ModularPlusCalMappingVariable variable = mapping.getVariable();
				UID varUID = registry.followReference(variable.getUID());
				if (seenVars.containsKey(varUID)) {
					// 0-indexing
					signature[seenVars.get(varUID)] = variable.isFunctionCall();
				} else if (variable instanceof ModularPlusCalMappingVariablePosition) {
					signature[((ModularPlusCalMappingVariablePosition) variable).getPosition() - 1] =
							variable.isFunctionCall();
				}
			}
			Optional<boolean[]> optionalExistingSignature = registry.getSignature(archetype.getUID());
			if (!optionalExistingSignature.isPresent()) {
				registry.putSignature(archetype.getUID(), signature);
				archetypesToInstance.put(archetype.getUID(), instance);
				continue;
			}
			boolean[] existingSignature = optionalExistingSignature.get();
			for (int i = 0; i < signature.length; i++) {
				if (existingSignature[i] != signature[i]) {
					ctx.error(new InconsistentInstantiationIssue(
							instance, archetypesToInstance.get(archetype.getUID())));
					break;
				}
			}
		}
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			Set<UID> nonRefParams = new HashSet<>();
			for (PlusCalVariableDeclaration param : archetype.getParams()) {
				if (!param.isRef()) {
					nonRefParams.add(param.getUID());
				}
			}
			ModularPlusCalModificationValidationVisitor visitor =
					new ModularPlusCalModificationValidationVisitor(ctx, registry, nonRefParams);
			Map<UID, Boolean> functionMapped = new HashMap<>();
			boolean[] signature = registry.getSignature(archetype.getUID())
					.orElseGet(() -> new boolean[archetype.getParams().size()]);
			List<PlusCalVariableDeclaration> params = archetype.getParams();
			for (int i = 0; i < params.size(); i++) {
				PlusCalVariableDeclaration param = params.get(i);
				functionMapped.put(param.getUID(), signature[i]);
			}
			for (PlusCalStatement statement : archetype.getBody()) {
				statement.accept(visitor);
				statement.accept(new ModularPlusCalStatementValidationVisitor(ctx, registry, functionMapped));
			}
		}
	}
}
