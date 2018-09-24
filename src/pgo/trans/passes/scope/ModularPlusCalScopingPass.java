package pgo.trans.passes.scope;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAModule;
import pgo.model.tla.TLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;
import pgo.trans.intermediate.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.stream.Stream;

public class ModularPlusCalScopingPass {
	private ModularPlusCalScopingPass() {}

	public static DefinitionRegistry perform(IssueContext ctx, TLAModule module,
	                                         ModularPlusCalBlock modularPlusCalBlock,
	                                         TLAModuleLoader loader, Map<String, TLAExpression> constantDefinitions) {
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

		TLAScopeBuilder modularPlusCalScope = tlaScope.makeNestedScope();

		// scope archetypes first, as they don't have access to global PlusCal variables
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			registry.addArchetype(archetype);
			modularPlusCalScope.defineGlobal(archetype.getName(), archetype.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(),
					modularPlusCalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			Stream.concat(archetype.getArguments().stream(), archetype.getVariables().stream())
					.forEach(decl -> {
				decl.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
				registry.addLocalVariable(decl.getUID());
				if (argScope.declare(decl.getName().getValue(), decl.getUID())) {
					args.put(decl.getName().getValue(), decl.getUID());
				}
			});

			TLAScopeBuilder archetypeScope = new TLAScopeBuilder(
					ctx, args, new ChainMap<>(modularPlusCalScope.getDefinitions()),
					modularPlusCalScope.getReferences());

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, archetypeScope));
			}

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(
						ctx, archetypeScope, registry, loader, new HashSet<>()));
			}
		}

		for (PlusCalVariableDeclaration decl : modularPlusCalBlock.getVariables()) {
			modularPlusCalScope.declare(decl.getName().getValue(), decl.getUID());
			registry.addGlobalVariable(decl.getUID());
			decl.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, registry, loader, new HashSet<>()));
		}

		for (TLAUnit unit : modularPlusCalBlock.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, modularPlusCalScope, registry, loader, new HashSet<>()));
		}

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

		return registry;
	}
}
