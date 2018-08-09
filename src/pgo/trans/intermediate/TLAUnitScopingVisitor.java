package pgo.trans.intermediate;


import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import pgo.errors.IssueContext;
import pgo.model.tla.TLAAssumption;
import pgo.model.tla.TLAConstantDeclaration;
import pgo.model.tla.TLAFunction;
import pgo.model.tla.TLAFunctionDefinition;
import pgo.model.tla.TLAIdentifier;
import pgo.model.tla.TLAInstance;
import pgo.model.tla.TLAModule;
import pgo.model.tla.TLAModuleDefinition;
import pgo.model.tla.TLAOpDecl;
import pgo.model.tla.TLAOperatorDefinition;
import pgo.model.tla.TLAQuantifierBound;
import pgo.model.tla.TLATheorem;
import pgo.model.tla.TLAUnit;
import pgo.model.tla.TLAUnitVisitor;
import pgo.model.tla.TLAVariableDeclaration;
import pgo.modules.ModuleNotFoundError;
import pgo.modules.NoModulesFoundInFileError;
import pgo.modules.TLAModuleLoader;
import pgo.parser.ParseFailureException;
import pgo.scope.UID;
import pgo.trans.passes.tlaparse.TLAParserIssue;

public class TLAUnitScopingVisitor extends TLAUnitVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private TLAScopeBuilder builder;
	private DefinitionRegistry registry;
	private TLAModuleLoader loader;
	private Set<String> moduleRecursionSet;

	public TLAUnitScopingVisitor(IssueContext ctx, TLAScopeBuilder builder, DefinitionRegistry registry,
			TLAModuleLoader loader, Set<String> moduleRecursionSet) {
		this.ctx = ctx;
		this.builder = builder;
		this.registry = registry;
		this.loader = loader;
		this.moduleRecursionSet = moduleRecursionSet;
	}

	public static void scopeModule(TLAModule module, IssueContext ctx, TLAScopeBuilder scope,
								   DefinitionRegistry registry, TLAModuleLoader loader,
								   Set<String> recursionSet) {
		Set<String> innerRecursionSet = new HashSet<>(recursionSet);
		innerRecursionSet.add(module.getName().getId());

		module = module.copy();
		TLABuiltins.getUniversalBuiltIns().addDefinitionsToRegistry(registry);

		for (TLAIdentifier ext : module.getExtends()) {
			if (TLABuiltins.isBuiltinModule(ext.getId())) {
				BuiltinModule m = TLABuiltins.findBuiltinModule(ext.getId());
				m.addDefinitionsToScope(scope);
				m.addDefinitionsToRegistry(registry);
			} else {
				IssueContext nestedCtx = ctx.withContext(new WhileLoadingUnit(ext));
				// take all variables, but only global definitions
				TLAScopeBuilder extendingScope = new TLAExtendsScopeBuilder(nestedCtx, scope.getDeclarations(),
						TLABuiltins.getInitialDefinitions(), scope.getReferences(), scope, false);
				loadModule(ext.getId(), nestedCtx, extendingScope, registry, loader, innerRecursionSet);
			}
		}

		for (TLAUnit unit : module.getPreTranslationUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, scope, registry, loader, innerRecursionSet));
		}
		// TODO: do something more interesting with the rest of the units
	}

	public static void loadModule(String name, IssueContext ctx, TLAScopeBuilder scope, DefinitionRegistry registry,
	                              TLAModuleLoader loader, Set<String> recursionSet) {
		if (TLABuiltins.isBuiltinModule(name)) {
			TLABuiltins.findBuiltinModule(name).addDefinitionsToScope(scope);
		} else if (recursionSet.contains(name)) {
			ctx.error(new CircularModuleReferenceIssue(name));
		} else {
			try {
				TLAModule module = registry.findModule(name);
				if (module == null) {
					module = loader.loadModule(name);
					registry.addModule(module);
				}

				module = module.copy();

				scopeModule(module, ctx, scope, registry, loader, recursionSet);

			} catch (ModuleNotFoundError e) {
				ctx.error(new ModuleNotFoundIssue(e.getModuleName(), e.getPathsChecked()));
			} catch (IOException e) {
				ctx.error(new IOErrorIssue(e));
			} catch (ParseFailureException e) {
				ctx.error(new TLAParserIssue(e.getReason()));
			} catch (NoModulesFoundInFileError e) {
				ctx.error(new NoModulesFoundInFileIssue());
			}
		}
	}

	private void checkInstanceSubstitutions(IssueContext ctx, Map<String, UID> decls, List<TLAInstance.Remapping> remappings, TLAScopeBuilder outerScope) {
		Set<String> remapped = new HashSet<>();

		for (TLAInstance.Remapping remap : remappings) {
			// make sure the expressions we're substituting in are also well scoped
			remap.getTo().accept(new TLAExpressionScopingVisitor(outerScope, registry, loader, moduleRecursionSet));

			if (decls.containsKey(remap.getFrom().getId())) {
				remapped.add(remap.getFrom().getId());
			} else {
				ctx.error(new ModuleSubstitutionNotFoundIssue(remap.getFrom()));
			}
		}

		for (Map.Entry<String, UID> entry : decls.entrySet()) {
			if (!remapped.contains(entry.getKey())) {
				// by default, remappings that are not specified remap to themselves
				// unlikely, but check if this works
				outerScope.reference(entry.getKey(), entry.getValue());
			}
		}
	}

	@Override
	public Void visit(TLAInstance pGoTLAInstance) throws RuntimeException {
		IssueContext nestedCtx = ctx.withContext(new WhileLoadingUnit(pGoTLAInstance));
		TLAScopeBuilder instanceScope = new TLAInstanceScopeBuilder(
				nestedCtx, new HashMap<>(), new HashMap<>(), builder.getReferences(), builder, null, pGoTLAInstance.isLocal());

		loadModule(pGoTLAInstance.getModuleName().getId(), nestedCtx, instanceScope, registry, loader, moduleRecursionSet);

		checkInstanceSubstitutions(ctx, instanceScope.getDeclarations(), pGoTLAInstance.getRemappings(), builder);
		return null;
	}

	@Override
	public Void visit(TLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		registry.addFunctionDefinition(pGoTLAFunctionDefinition);

		if (pGoTLAFunctionDefinition.isLocal()) {
			builder.defineLocal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getName().getUID());
		} else {
			builder.defineGlobal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getName().getUID());
		}
		TLAScopeBuilder argScope = builder.makeNestedScope();
		TLAFunction fn = pGoTLAFunctionDefinition.getFunction();
		for (TLAQuantifierBound qb : fn.getArguments()) {
			for (TLAIdentifier id : qb.getIds()) {
				argScope.defineLocal(id.getId(), id.getUID());
				registry.addLocalVariable(id.getUID());
			}
			qb.getSet().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		}
		fn.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		registry.addOperator(pGoTLAOperator.getName().getUID(), new CompiledOperatorAccessor(pGoTLAOperator));

		if (pGoTLAOperator.isLocal()) {
			builder.defineLocal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getName().getUID());
		} else {
			builder.defineGlobal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getName().getUID());
		}
		TLAScopeBuilder argScope = builder.makeNestedScope();
		for (TLAOpDecl op : pGoTLAOperator.getArgs()) {
			argScope.defineLocal(op.getName().getId(), op.getName().getUID());
			registry.addLocalVariable(op.getName().getUID());
		}
		pGoTLAOperator.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLATheorem pGoTLATheorem) throws RuntimeException {
		pGoTLATheorem.getTheorem().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAModule pGoTLAModule) throws RuntimeException {
		ctx.error(new UnsupportedFeatureIssue("PGo does not support nested modules"));
		return null;
	}

	@Override
	public Void visit(TLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		for (TLAIdentifier id : pGoTLAVariableDeclaration.getVariables()) {
			builder.declare(id.getId(), id.getUID());
			registry.addGlobalVariable(id.getUID());
		}
		return null;
	}

	@Override
	public Void visit(TLAConstantDeclaration TLAConstantDeclaration) throws RuntimeException {
		for (TLAOpDecl op : TLAConstantDeclaration.getConstants()) {
			builder.declare(op.getName().getId(), op.getName().getUID());
			registry.addConstant(op.getName().getUID(), op.getName().getId());
		}
		return null;
	}

	@Override
	public Void visit(TLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		IssueContext nestedCtx = ctx.withContext(new WhileLoadingUnit(pGoTLAModuleDefinition));
		TLAScopeBuilder instanceScope = new TLAInstanceScopeBuilder(
				nestedCtx, new HashMap<>(), new HashMap<>(), builder.getReferences(), builder,
				pGoTLAModuleDefinition.getName().getId(), pGoTLAModuleDefinition.isLocal());

		TLAScopeBuilder argScope = builder.makeNestedScope();
		for (TLAOpDecl arg : pGoTLAModuleDefinition.getArgs()) {
			argScope.defineLocal(arg.getName().getId(), arg.getUID());
		}

		loadModule(pGoTLAModuleDefinition.getInstance().getModuleName().getId(), nestedCtx, instanceScope, registry, loader, moduleRecursionSet);

		checkInstanceSubstitutions(ctx, instanceScope.getDeclarations(), pGoTLAModuleDefinition.getInstance().getRemappings(), argScope);
		return null;
	}

	@Override
	public Void visit(TLAAssumption TLAAssumption) throws RuntimeException {
		TLAAssumption.getAssumption().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

}
