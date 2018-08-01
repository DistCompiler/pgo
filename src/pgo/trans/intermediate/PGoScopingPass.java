package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PGoScopingPass {

	private PGoScopingPass() {}

	public static DefinitionRegistry perform(IssueContext ctx, PGoTLAModule module, Algorithm algorithm,
			TLAModuleLoader loader, Map<String, PGoTLAExpression> constantDefinitions){
		DefinitionRegistry registry = new DefinitionRegistry();
		TLAScopeBuilder tlaScope = new TLAScopeBuilder(ctx, registry.getReferences());

		TLAUnitScopingVisitor.scopeModule(module, ctx, tlaScope, registry, loader, new HashSet<>());

		// resolve user-provided constant values from the config file
		for (UID id : registry.getConstants()) {
			String name = registry.getConstantName(id);
			if (!constantDefinitions.containsKey(name)) {
				ctx.error(new ConstantWithNoValueIssue(name, id));
			} else {
				PGoTLAExpression value = constantDefinitions.get(name);
				value.accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.setConstantValue(id, value);
			}
		}

		TLAScopeBuilder pcalScope = tlaScope.makeNestedScope();

		for (VariableDeclaration decl : algorithm.getVariables()) {
			pcalScope.declare(decl.getName().getValue(), decl.getUID());
			registry.addGlobalVariable(decl.getUID());
			decl.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
		}

		for (PGoTLAUnit unit : algorithm.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, pcalScope, registry, loader, new HashSet<>()));
		}

		algorithm.getProcesses().accept(
				new PlusCalProcessesScopingVisitor(ctx, pcalScope, tlaScope, registry, loader, new HashSet<>()));

		for (Procedure proc : algorithm.getProcedures()) {

			registry.addProcedure(proc);

			pcalScope.defineGlobal(proc.getName(), proc.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(), pcalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			for (VariableDeclaration arg : proc.getArguments()) {
				arg.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.addLocalVariable(arg.getUID());
				if (argScope.declare(arg.getName().getValue(), arg.getUID())) {
					args.put(arg.getName().getValue(), arg.getUID());
				}
			}
			// TODO: wait those aren't in the spec...
			/*for (VariableDeclaration arg : proc.getVariables()) {
				if (arg.getValue() != null) {
					arg.getValue().accept(new PGoTLAExpressionScopingVisitor(tlaScope));
				}
				procScope.declare(arg.getName(), arg.getUID());
			}*/

			TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, args, new ChainMap<>(pcalScope.getDefinitions()), pcalScope.getReferences());

			for (LabeledStatements stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}

			for (LabeledStatements stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, new HashSet<>()));
			}
		}

		return registry;
	}

}
