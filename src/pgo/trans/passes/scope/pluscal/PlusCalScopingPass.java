package pgo.trans.passes.scope.pluscal;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;
import pgo.trans.intermediate.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class PlusCalScopingPass {
	private PlusCalScopingPass() {}

	public static void perform(IssueContext ctx, DefinitionRegistry registry, TLAModuleLoader loader,
	                           TLAScopeBuilder tlaScope, TLAScopeBuilder modularPlusCalScope,
	                           ModularPlusCalBlock modularPlusCalBlock) {

		modularPlusCalBlock.getProcesses().accept(
				new PlusCalProcessesScopingVisitor(ctx, modularPlusCalScope, tlaScope, registry, loader, new HashSet<>()));

		for (PlusCalProcedure proc : modularPlusCalBlock.getProcedures()) {
			registry.addProcedure(proc);
			modularPlusCalScope.defineGlobal(proc.getName(), proc.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(),
					modularPlusCalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			for (PlusCalVariableDeclaration arg : proc.getArguments()) {
				arg.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.addLocalVariable(arg.getUID());
				if (argScope.declare(arg.getName().getValue(), arg.getUID())) {
					args.put(arg.getName().getValue(), arg.getUID());
				}
			}

			TLAScopeBuilder procScope = new TLAScopeBuilder(
					ctx, args, new ChainMap<>(modularPlusCalScope.getDefinitions()),
					modularPlusCalScope.getReferences());

			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}

			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, new HashSet<>()));
			}
		}
	}
}
