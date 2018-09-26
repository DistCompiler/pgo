package pgo.trans.passes.scope.tla;

import pgo.errors.IssueContext;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAModule;
import pgo.modules.TLAModuleLoader;
import pgo.scope.UID;
import pgo.trans.intermediate.*;

import java.util.HashSet;
import java.util.Map;

public class TLAScopingPass {
	private TLAScopingPass() {}

	public static TLAScopeBuilder perform(IssueContext ctx, DefinitionRegistry registry,
	                                      TLAModuleLoader loader, Map<String, TLAExpression> constantDefinitions, TLAModule module) {
		TLAScopeBuilder tlaScope = new TLAScopeBuilder(ctx, registry.getReferences());

		TLAUnitScopingVisitor.scopeModule(module, ctx, tlaScope, registry, loader, new HashSet<>());

		// resolve user-provided constant values from the config file
		for (UID id : registry.getConstants()) {
			String name = registry.getConstantName(id);
			if (!constantDefinitions.containsKey(name)) {
				ctx.error(new ConstantWithNoValueIssue(name, id));
			} else {
				TLAExpression value = constantDefinitions.get(name);
				value.accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.setConstantValue(id, value);
			}
		}

		return tlaScope;
	}
}
