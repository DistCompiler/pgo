package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAModule;
import pgo.model.tla.TLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PGoScopingPass {

	private PGoScopingPass() {}

	public static DefinitionRegistry perform(IssueContext ctx, TLAModule module, PlusCalAlgorithm plusCalAlgorithm,
											 TLAModuleLoader loader, Map<String, TLAExpression> constantDefinitions){
		DefinitionRegistry registry = new DefinitionRegistry();
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

		TLAScopeBuilder pcalScope = tlaScope.makeNestedScope();

		for (PlusCalVariableDeclaration decl : plusCalAlgorithm.getVariables()) {
			pcalScope.declare(decl.getName().getValue(), decl.getUID());
			registry.addGlobalVariable(decl.getUID());
			decl.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
		}

		for (TLAUnit unit : plusCalAlgorithm.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, pcalScope, registry, loader, new HashSet<>()));
		}

		plusCalAlgorithm.getProcesses().accept(
				new PlusCalProcessesScopingVisitor(ctx, pcalScope, tlaScope, registry, loader, new HashSet<>()));

		for (PlusCalProcedure proc : plusCalAlgorithm.getProcedures()) {

			registry.addProcedure(proc);

			pcalScope.defineGlobal(proc.getName(), proc.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(), pcalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			for (PlusCalVariableDeclaration arg : proc.getArguments()) {
				arg.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.addLocalVariable(arg.getUID());
				if (argScope.declare(arg.getName().getValue(), arg.getUID())) {
					args.put(arg.getName().getValue(), arg.getUID());
				}
			}
			// TODO: wait those aren't in the spec...
			/*for (PlusCalVariableDeclaration arg : proc.getVariables()) {
				if (arg.getValue() != null) {
					arg.getValue().accept(new PGoTLAExpressionScopingVisitor(tlaScope));
				}
				procScope.declare(arg.getName(), arg.getUID());
			}*/

			TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, args, new ChainMap<>(pcalScope.getDefinitions()), pcalScope.getReferences());

			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}

			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, new HashSet<>()));
			}
		}

		return registry;
	}

}
