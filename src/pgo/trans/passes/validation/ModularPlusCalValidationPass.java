package pgo.trans.passes.validation;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.HashSet;
import java.util.Set;

public class ModularPlusCalValidationPass {
	private ModularPlusCalValidationPass() {}

	public static void perform(IssueContext ctx, ModularPlusCalBlock mpcal) {
		mpcal.accept(new ModularPlusCalValidationVisitor(ctx));
	}

	public static void performPostScoping(TopLevelIssueContext ctx, DefinitionRegistry registry,
	                                      ModularPlusCalBlock modularPlusCalBlock) {
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			Set<UID> nonRefParams = new HashSet<>();
			for (PlusCalVariableDeclaration param : archetype.getParams()) {
				if (!param.isRef()) {
					nonRefParams.add(param.getUID());
				}
			}
			ModularPlusCalModificationValidationVisitor visitor =
					new ModularPlusCalModificationValidationVisitor(ctx, registry, nonRefParams);
			for (PlusCalStatement statement : archetype.getBody()) {
				statement.accept(visitor);
			}
		}
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Set<UID> seenVars = new HashSet<>();
			for (TLAExpression argument : instance.getArguments()) {
				if (argument instanceof TLAGeneralIdentifier || argument instanceof TLARef) {
					UID varUID = registry.followReference(argument.getUID());
					if (seenVars.contains(varUID)) {
						ctx.error(new VariableMappedMultipleTimesIssue(varUID, instance));
					}
					seenVars.add(varUID);
				}
			}
		}
	}
}
