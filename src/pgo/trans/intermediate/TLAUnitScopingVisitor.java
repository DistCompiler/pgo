package pgo.trans.intermediate;


import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import pgo.errors.IssueContext;
import pgo.lexer.PGoTLALexerException;
import pgo.model.tla.PGoTLAAssumption;
import pgo.model.tla.PGoTLAConstantDeclaration;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAModuleDefinition;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLATheorem;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PGoTLAUnitVisitor;
import pgo.model.tla.PGoTLAVariableDeclaration;
import pgo.modules.ModuleNotFoundError;
import pgo.modules.NoModulesFoundInFileError;
import pgo.modules.TLAModuleLoader;
import pgo.parser.TLAParseException;
import pgo.scope.UID;

public class TLAUnitScopingVisitor extends PGoTLAUnitVisitor<Void, RuntimeException> {

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

	public static void scopeModule(PGoTLAModule module, IssueContext ctx, TLAScopeBuilder scope,
	                               DefinitionRegistry registry, TLAModuleLoader loader,
	                               Set<String> recursionSet) {
		Set<String> innerRecursionSet = new HashSet<>(recursionSet);
		innerRecursionSet.add(module.getName().getId());

		module = module.copy();
		TLABuiltins.getUniversalBuiltins().addDefinitionsToRegistry(registry);

		for (PGoTLAIdentifier ext : module.getExtends()) {
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

		for (PGoTLAUnit unit : module.getPreTranslationUnits()) {
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
				PGoTLAModule module = registry.findModule(name);
				if (module == null) {
					module = loader.loadModule(name);
					registry.addModule(module);
				}

				module = module.copy();

				scopeModule(module, ctx, scope, registry, loader, recursionSet);

			} catch (PGoTLALexerException e) {
				ctx.error(new TLALexerIssue(e));
			} catch (ModuleNotFoundError e) {
				ctx.error(new ModuleNotFoundIssue(e.getModuleName(), e.getPathsChecked()));
			} catch (IOException e) {
				ctx.error(new IOErrorIssue(e));
			} catch (TLAParseException e) {
				ctx.error(new TLAParserIssue(e.getReason()));
			} catch (NoModulesFoundInFileError e) {
				ctx.error(new NoModulesFoundInFileIssue());
			}
		}
	}

	private void checkInstanceSubstitutions(IssueContext ctx, Map<String, UID> decls, List<PGoTLAInstance.Remapping> remappings, TLAScopeBuilder outerScope) {
		Set<String> remapped = new HashSet<>();

		for (PGoTLAInstance.Remapping remap : remappings) {
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
	public Void visit(PGoTLAInstance pGoTLAInstance) throws RuntimeException {
		IssueContext nestedCtx = ctx.withContext(new WhileLoadingUnit(pGoTLAInstance));
		TLAScopeBuilder instanceScope = new TLAInstanceScopeBuilder(
				nestedCtx, new HashMap<>(), new HashMap<>(), builder.getReferences(), builder, null, pGoTLAInstance.isLocal());

		loadModule(pGoTLAInstance.getModuleName().getId(), nestedCtx, instanceScope, registry, loader, moduleRecursionSet);

		checkInstanceSubstitutions(ctx, instanceScope.getDeclarations(), pGoTLAInstance.getRemappings(), builder);
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionDefinition pGoTLAFunctionDefinition) throws RuntimeException {
		registry.addFunctionDefinition(pGoTLAFunctionDefinition);

		if (pGoTLAFunctionDefinition.isLocal()) {
			builder.defineLocal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getName().getUID());
		} else {
			builder.defineGlobal(pGoTLAFunctionDefinition.getName().getId(), pGoTLAFunctionDefinition.getName().getUID());
		}
		TLAScopeBuilder argScope = builder.makeNestedScope();
		PGoTLAFunction fn = pGoTLAFunctionDefinition.getFunction();
		for (PGoTLAQuantifierBound qb : fn.getArguments()) {
			for (PGoTLAIdentifier id : qb.getIds()) {
				argScope.defineLocal(id.getId(), id.getUID());
				registry.addLocalVariable(id.getUID());
			}
			qb.getSet().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		}
		fn.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorDefinition pGoTLAOperator) throws RuntimeException {
		registry.addOperator(pGoTLAOperator.getName().getUID(), new CompiledOperatorAccessor(pGoTLAOperator));

		if (pGoTLAOperator.isLocal()) {
			builder.defineLocal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getName().getUID());
		} else {
			builder.defineGlobal(pGoTLAOperator.getName().getId(), pGoTLAOperator.getName().getUID());
		}
		TLAScopeBuilder argScope = builder.makeNestedScope();
		for (PGoTLAOpDecl op : pGoTLAOperator.getArgs()) {
			argScope.defineLocal(op.getName().getId(), op.getName().getUID());
			registry.addLocalVariable(op.getName().getUID());
		}
		pGoTLAOperator.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PGoTLATheorem pGoTLATheorem) throws RuntimeException {
		pGoTLATheorem.getTheorem().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PGoTLAModule pGoTLAModule) throws RuntimeException {
		ctx.error(new UnsupportedFeatureIssue("PGo does not support nested modules"));
		return null;
	}

	@Override
	public Void visit(PGoTLAVariableDeclaration pGoTLAVariableDeclaration) throws RuntimeException {
		for (PGoTLAIdentifier id : pGoTLAVariableDeclaration.getVariables()) {
			builder.declare(id.getId(), id.getUID());
			registry.addGlobalVariable(id.getUID());
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAConstantDeclaration pGoTLAConstantDeclaration) throws RuntimeException {
		for (PGoTLAOpDecl op : pGoTLAConstantDeclaration.getConstants()) {
			builder.declare(op.getName().getId(), op.getName().getUID());
			registry.addConstant(op.getName().getUID(), op.getName().getId());
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAModuleDefinition pGoTLAModuleDefinition) throws RuntimeException {
		IssueContext nestedCtx = ctx.withContext(new WhileLoadingUnit(pGoTLAModuleDefinition));
		TLAScopeBuilder instanceScope = new TLAInstanceScopeBuilder(
				nestedCtx, new HashMap<>(), new HashMap<>(), builder.getReferences(), builder,
				pGoTLAModuleDefinition.getName().getId(), pGoTLAModuleDefinition.isLocal());

		TLAScopeBuilder argScope = builder.makeNestedScope();
		for (PGoTLAOpDecl arg : pGoTLAModuleDefinition.getArgs()) {
			argScope.defineLocal(arg.getName().getId(), arg.getUID());
		}

		loadModule(pGoTLAModuleDefinition.getInstance().getModuleName().getId(), nestedCtx, instanceScope, registry, loader, moduleRecursionSet);

		checkInstanceSubstitutions(ctx, instanceScope.getDeclarations(), pGoTLAModuleDefinition.getInstance().getRemappings(), argScope);
		return null;
	}

	@Override
	public Void visit(PGoTLAAssumption pGoTLAAssumption) throws RuntimeException {
		pGoTLAAssumption.getAssumption().accept(new TLAExpressionScopingVisitor(builder, registry, loader, moduleRecursionSet));
		return null;
	}

}
