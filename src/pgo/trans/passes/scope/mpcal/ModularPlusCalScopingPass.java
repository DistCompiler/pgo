package pgo.trans.passes.scope.mpcal;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.PlusCalStatement;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLARef;
import pgo.model.tla.TLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;
import pgo.trans.intermediate.*;
import pgo.trans.passes.expansion.*;

import java.util.*;
import java.util.stream.Stream;

public class ModularPlusCalScopingPass {
	private ModularPlusCalScopingPass() {}

	public static TLAScopeBuilder perform(IssueContext ctx, DefinitionRegistry registry, TLAModuleLoader loader,
	                           TLAScopeBuilder tlaScope, ModularPlusCalBlock modularPlusCalBlock) {
		TLAScopeBuilder modularPlusCalScope = tlaScope.makeNestedScope();

		// mapping macros, and archetypes don't have access to PlusCal global variables but needs access to TLA+ units
		// in define block
		// FIXME? previous scoping code scopes global variables before TLA+ units
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
		for (PlusCalVariableDeclaration variableDeclaration : modularPlusCalBlock.getVariables()) {
			modularPlusCalScope.declare(variableDeclaration.getName().getValue(), variableDeclaration.getUID());
			registry.addGlobalVariable(variableDeclaration.getUID());
			variableDeclaration.getValue().accept(new TLAExpressionScopingVisitor(
					tlaScope, registry, loader, new HashSet<>()));
		}

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
			Set<String> refs = new HashSet<>();
			for (TLAExpression expression : instance.getParams()) {
				if (expression instanceof TLARef) {
					refs.add(((TLARef) expression).getTarget());
				}
				expression.accept(new TLAExpressionScopingVisitor(
						modularPlusCalScope, registry, loader, new HashSet<>()));
			}
			mappingNames.removeAll(refs);
			if (mappingNames.size() != 0) {
				ctx.error(new MismatchedRefMappingIssue(instance, mappingNames));
			}
		}

		return modularPlusCalScope;
	}
}
