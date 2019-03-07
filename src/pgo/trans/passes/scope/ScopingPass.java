package pgo.trans.passes.scope;

import pgo.Unreachable;
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
import java.util.List;

public class ScopingPass {
	private ScopingPass() {}

	private static void scopeVariables(
			IssueContext ctx,
			boolean isMPCal,
			List<PlusCalVariableDeclaration> variables,
			DefinitionRegistry registry,
			TLAModuleLoader loader,
			TLAScopeBuilder validateScope,
			TLAScopeBuilder newScope,
			Map<String, UID> variablesMap)
	{
		for (PlusCalVariableDeclaration variableDeclaration : variables) {
			variableDeclaration.getValue().accept(new TLAExpressionScopingVisitor(
					ctx, validateScope, registry, loader, new HashSet<>(), !isMPCal));
			registry.addLocalVariable(variableDeclaration.getUID());
			if (newScope.declare(variableDeclaration.getName().getValue(), variableDeclaration.getUID())) {
				variablesMap.put(variableDeclaration.getName().getValue(), variableDeclaration.getUID());
			}
		}
	}

	private static void handleNameMapping(IssueContext ctx, ModularPlusCalMapping mapping, String variableName,
	                                      TLAScopeBuilder modularPlusCalScope,
	                                      Map<String,ModularPlusCalMapping> mappedNames) {
		if (mappedNames.containsKey(variableName)) {
			ctx.error(new MultipleMappingIssue(mappedNames.get(variableName), mapping));
			return;
		}
		modularPlusCalScope.reference(mapping.getTarget().getName(), mapping.getTarget().getUID());
		modularPlusCalScope.reference(variableName, mapping.getVariable().getUID());
		mappedNames.put(variableName, mapping);
	}
	public static DefinitionRegistry perform(IssueContext ctx, boolean resolveConstants, TLAModuleLoader loader,
	                                         Map<String, TLAExpression> constantDefinitions, TLAModule module,
	                                         ModularPlusCalBlock modularPlusCalBlock) {
		DefinitionRegistry registry = new DefinitionRegistry();
		TLAScopeBuilder tlaScope = new TLAScopeBuilder(ctx, registry.getReferences());

		TLAUnitScopingVisitor.scopeModule(module, ctx, tlaScope, registry, loader, new HashSet<>());

		// resolve user-provided constant values from the config file. They are only required
		// to be defined if compiling a PlusCal (not MPCal) specification
		for (UID id : registry.getConstants()) {
			String name = registry.getConstantName(id);
			if (constantDefinitions.containsKey(name)) {
				TLAExpression value = constantDefinitions.get(name);
				value.accept(new TLAExpressionScopingVisitor(ctx, tlaScope, registry, loader, new HashSet<>(), resolveConstants));
				registry.setConstantValue(id, value);
			}
		}

		TLAScopeBuilder modularPlusCalScope = tlaScope.makeNestedScope();

		for (TLAUnit unit : modularPlusCalBlock.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, tlaScope, registry, loader, new HashSet<>()));
		}

		for (PlusCalVariableDeclaration variableDeclaration : modularPlusCalBlock.getVariables()) {
			modularPlusCalScope.declare(variableDeclaration.getName().getValue(), variableDeclaration.getUID());
			registry.addGlobalVariable(variableDeclaration.getUID());
			variableDeclaration.getValue().accept(new TLAExpressionScopingVisitor(
					ctx, modularPlusCalScope, registry, loader, new HashSet<>(), false));
		}

		for (PlusCalProcedure proc : modularPlusCalBlock.getProcedures()) {
			registry.addProcedure(proc);
			modularPlusCalScope.defineGlobal(proc.getName(), proc.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(),
					modularPlusCalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			scopeVariables(ctx, resolveConstants, proc.getParams(), registry, loader, tlaScope, argScope, args);
			scopeVariables(ctx, resolveConstants, proc.getVariables(), registry, loader, argScope, argScope, args);

			TLAScopeBuilder procScope = new TLAScopeBuilder(
					ctx, args, new ChainMap<>(modularPlusCalScope.getDefinitions()),
					modularPlusCalScope.getReferences());

			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(procScope));
			}

			// procedures always need to have defined constants
			for (PlusCalStatement stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, new HashSet<>(), resolveConstants));
			}
		}

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			registry.addArchetype(archetype);
			modularPlusCalScope.defineGlobal(archetype.getName(), archetype.getUID());

			TLAScopeBuilder argScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), tlaScope.getDefinitions(),
					tlaScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());

			scopeVariables(ctx, resolveConstants, archetype.getParams(), registry, loader, tlaScope, argScope, args);
			scopeVariables(ctx, resolveConstants, archetype.getVariables(), registry, loader, argScope, argScope, args);

			TLAScopeBuilder archetypeScope = new TLAScopeBuilder(
					ctx, args, new ChainMap<>(tlaScope.getDefinitions()), tlaScope.getReferences());
			archetypeScope.defineLocal("self", archetype.getSelfVariableUID());
			registry.addLocalVariable(archetype.getSelfVariableUID());

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(archetypeScope));
			}

			for (PlusCalStatement stmts : archetype.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(
						ctx, archetypeScope, registry, loader, new HashSet<>(), resolveConstants));
			}
		}

		for (ModularPlusCalMappingMacro mappingMacro : modularPlusCalBlock.getMappingMacros()) {
			registry.addMappingMacro(mappingMacro);
			modularPlusCalScope.defineGlobal(mappingMacro.getName(), mappingMacro.getUID());

			Map<String, UID> readArgs = new ChainMap<>(tlaScope.getDeclarations());
			readArgs.put("$variable", mappingMacro.getSpecialVariableVariableUID());
			readArgs.put("self", mappingMacro.getSelfVariableUID());
			TLAScopeBuilder readBodyScope = new TLAScopeBuilder(ctx, readArgs,
					new ChainMap<>(tlaScope.getDefinitions()), tlaScope.getReferences());

			for (PlusCalStatement statement : mappingMacro.getReadBody()) {
				// TODO make this work with qualified macro name
				statement.accept(new PlusCalStatementScopingVisitor(
						ctx, readBodyScope, registry, loader, new HashSet<>(),
						MappingMacroTLAExpressionScopingVisitor::new, false));
			}

			Map<String, UID> writeArgs = new ChainMap<>(tlaScope.getDeclarations());
			writeArgs.put("$variable", mappingMacro.getSpecialVariableVariableUID());
			writeArgs.put("$value", mappingMacro.getSpecialVariableValueUID());
			writeArgs.put("self", mappingMacro.getSelfVariableUID());
			TLAScopeBuilder writeBodyScope = new TLAScopeBuilder(ctx, writeArgs,
					new ChainMap<>(tlaScope.getDefinitions()), tlaScope.getReferences());

			for (PlusCalStatement statement : mappingMacro.getWriteBody()) {
				// TODO make this work with qualified macro name
				statement.accept(new PlusCalStatementScopingVisitor(
						ctx, writeBodyScope, registry, loader, new HashSet<>(),
						MappingMacroTLAExpressionScopingVisitor::new, false));
			}
		}

		// instances need access to global variables
		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			modularPlusCalScope.defineGlobal(instance.getName().getName().getValue(), instance.getName().getUID());
			TLAScopeBuilder instanceTLAScope = new TLAScopeBuilder(
					ctx, new ChainMap<>(tlaScope.getDeclarations()), modularPlusCalScope.getDefinitions(),
					modularPlusCalScope.getReferences());
			instance.getName().getValue().accept(
					new TLAExpressionScopingVisitor(ctx, tlaScope, registry, loader, new HashSet<>(),false));

			ModularPlusCalArchetype archetype = registry.findArchetype(instance.getTarget());
			if (archetype != null && instance.getArguments().size() != archetype.getParams().size()) {
				ctx.error(new InstanceArgumentCountMismatchIssue(instance, archetype));
				continue;
			} else if (archetype != null) {
				PlusCalStatementScopingVisitor.verifyRefMatching(ctx, archetype.getParams(), instance.getArguments());
			} else {
				ctx.error(new ArchetypeNotFoundIssue(instance, instance.getTarget()));
				continue;
			}

			Map<Integer, String> positionsToNames = new HashMap<>();
			List<TLAExpression> arguments = instance.getArguments();
			for (int i = 0; i < arguments.size(); i++) {
				TLAExpression argument = arguments.get(i);
				if (argument instanceof TLAGeneralIdentifier) {
					// 1-indexing
					positionsToNames.put(i+1, ((TLAGeneralIdentifier) argument).getName().getId());
				} else if (argument instanceof TLARef) {
					// 1-indexing
					positionsToNames.put(i+1, ((TLARef) argument).getTarget());
				}
			}

			Map<String, ModularPlusCalMapping> mappedNames = new HashMap<>();
			Map<Integer, ModularPlusCalMapping> mappedPositions = new HashMap<>();
			for (ModularPlusCalMapping mapping : instance.getMappings()) {
				if (mapping.getVariable() instanceof ModularPlusCalMappingVariableName) {
					String variableName = ((ModularPlusCalMappingVariableName) mapping.getVariable()).getName();
					handleNameMapping(ctx, mapping, variableName, modularPlusCalScope, mappedNames);
				} else if (mapping.getVariable() instanceof ModularPlusCalMappingVariablePosition) {
					// 1-indexing
					int pos = ((ModularPlusCalMappingVariablePosition) mapping.getVariable()).getPosition();
					if (pos <= 0 || pos > instance.getArguments().size()) {
						ctx.error(new DanglingReferenceIssue(mapping.getVariable().getUID()));
						continue;
					}
					if (mappedPositions.containsKey(pos)) {
						ctx.error(new MultipleMappingIssue(mappedPositions.get(pos), mapping));
						continue;
					}
					mappedPositions.put(pos, mapping);
					modularPlusCalScope.reference(
							archetype.getParams().get(pos-1).getUID(), mapping.getVariable().getUID());
					modularPlusCalScope.reference(mapping.getTarget().getName(), mapping.getTarget().getUID());
					if (positionsToNames.containsKey(pos)) {
						String variableName = positionsToNames.get(pos);
						handleNameMapping(ctx, mapping, variableName, modularPlusCalScope, mappedNames);
					}
				} else {
					throw new Unreachable();
				}
			}
			for (TLAExpression expression : instance.getArguments()) {
				expression.accept(new TLAExpressionScopingVisitor(
						ctx, instanceTLAScope, registry, loader, new HashSet<>(), false));
			}
		}

		modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesScopingVisitor(
				ctx, modularPlusCalScope, tlaScope, registry, loader, new HashSet<>(), resolveConstants));

		return registry;
	}
}
