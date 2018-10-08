package pgo.trans.passes.scope;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalProcedure;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;
import pgo.trans.intermediate.*;
import pgo.trans.passes.expansion.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

public class ScopingPass {
	private ScopingPass() {}

	public static DefinitionRegistry perform(IssueContext ctx, TLAModuleLoader loader,
	                                         Map<String,TLAExpression> constantDefinitions, TLAModule module,
	                                         ModularPlusCalBlock modularPlusCalBlock) {
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

		for (PlusCalVariableDeclaration variableDeclaration : modularPlusCalBlock.getVariables()) {
			modularPlusCalScope.declare(variableDeclaration.getName().getValue(), variableDeclaration.getUID());
			registry.addGlobalVariable(variableDeclaration.getUID());
			variableDeclaration.getValue().accept(new TLAExpressionScopingVisitor(
					tlaScope, registry, loader, new HashSet<>()));
		}

		for (TLAUnit unit : modularPlusCalBlock.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, modularPlusCalScope, registry, loader, new HashSet<>()));
		}

		Map<String, ModularPlusCalArchetype> archetypes = new HashMap<>();
		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			if (archetypes.containsKey(archetype.getName())) {
				ctx.error(new ArchetypeNameConflictIssue(archetypes.get(archetype.getName()), archetype));
			}
			archetypes.put(archetype.getName(), archetype);

			modularPlusCalScope.defineGlobal(archetype.getName(), archetype.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(),
					modularPlusCalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			Stream.concat(archetype.getArguments().stream(), archetype.getVariables().stream())
					.forEach(variableDeclaration -> {
						variableDeclaration.getValue().accept(new TLAExpressionScopingVisitor(
								tlaScope, registry, loader, new HashSet<>()));
						registry.addLocalVariable(variableDeclaration.getUID());
						if (argScope.declare(variableDeclaration.getName().getValue(), variableDeclaration.getUID())) {
							args.put(variableDeclaration.getName().getValue(), variableDeclaration.getUID());
						}
					});

			TLAScopeBuilder archetypeScope = new TLAScopeBuilder(
					ctx, args, new ChainMap<>(tlaScope.getDefinitions()), tlaScope.getReferences());
			archetypeScope.defineLocal("self", archetype.getUID());
			registry.addLocalVariable(archetype.getUID());

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, archetypeScope));
			}

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(
						ctx, archetypeScope, registry, loader, new HashSet<>()));
			}
		}

		Map<String, ModularPlusCalMappingMacro> mappingMacros = new HashMap<>();
		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			if (mappingMacros.containsKey(mappingMacro.getName())) {
				ctx.error(new MappingMacroNameConflictIssue(mappingMacros.get(mappingMacro.getName()), mappingMacro));
			}
			mappingMacros.put(mappingMacro.getName(), mappingMacro);

			for (PlusCalStatement statement : mappingMacro.getReadBody()) {
				statement.accept(new PlusCalStatementScopingVisitor(
						ctx, modularPlusCalScope, registry, loader, new HashSet<>()));
			}

			for (PlusCalStatement statement : mappingMacro.getWriteBody()) {
				statement.accept(new PlusCalStatementScopingVisitor(
						ctx, modularPlusCalScope, registry, loader, new HashSet<>()));
			}
		}

		// instances need access to global variables

		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			Set<String> mappingNames = new HashSet<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				if (!mappingMacros.containsKey(mapping.getTarget())) {
					ctx.error(new UnknownMappingTargetIssue(mapping));
				}
				mappingNames.add(mapping.getName().getValue());
			}
			if (!archetypes.containsKey(instance.getTarget())) {
				ctx.error(new UnknownArchetypeTargetIssue(instance));
				continue;
			}
			ModularPlusCalArchetype archetype = archetypes.get(instance.getTarget());
			if (instance.getParams().size() != archetype.getArguments().size()) {
				ctx.error(new InstanceArgumentCountMismatchIssue(instance, archetype));
				continue;
			}
			Set<String> mappedGlobals = new HashSet<>();
			for (TLAExpression expression : instance.getParams()) {
				if (expression instanceof TLARef) {
					mappedGlobals.add(((TLARef) expression).getTarget());
				} else if (expression instanceof TLAGeneralIdentifier) {
					mappedGlobals.add(((TLAGeneralIdentifier) expression).getName().getId());
				}
				expression.accept(new TLAExpressionScopingVisitor(
						modularPlusCalScope, registry, loader, new HashSet<>()));
			}
			mappingNames.removeAll(mappedGlobals);
			if (mappingNames.size() != 0) {
				ctx.error(new MismatchedRefMappingIssue(instance, mappingNames));
			}
		}

		modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesScopingVisitor(
				ctx, modularPlusCalScope, tlaScope, registry, loader, new HashSet<>()));

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
