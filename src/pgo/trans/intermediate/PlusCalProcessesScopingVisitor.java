package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.pcal.PlusCalMultiProcess;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PlusCalProcessesScopingVisitor extends PlusCalProcessesVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private TLAScopeBuilder builder;
	private TLAScopeBuilder tlaBuilder;
	private DefinitionRegistry registry;
	private TLAModuleLoader loader;
	private Set<String> moduleRecursionSet;

	public PlusCalProcessesScopingVisitor(IssueContext ctx, TLAScopeBuilder builder, TLAScopeBuilder tlaBuilder,
	                                      DefinitionRegistry registry, TLAModuleLoader loader, Set<String> moduleRecursionSet) {
		this.ctx = ctx;
		this.builder = builder;
		this.tlaBuilder = tlaBuilder;
		this.registry = registry;
		this.loader = loader;
		this.moduleRecursionSet = moduleRecursionSet;
	}

	@Override
	public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
		TLAScopeBuilder labelScope = new TLAScopeBuilder(ctx, new HashMap<>(), new ChainMap<>(builder.getDefinitions()), builder.getReferences());

		for (PlusCalLabeledStatements stmts : singleProcess.getLabeledStatements()) {
			stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, labelScope));
		}

		TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, builder.getDeclarations(), labelScope.getDefinitions(), builder.getReferences());
		for (PlusCalLabeledStatements stmts : singleProcess.getLabeledStatements()) {
			stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, moduleRecursionSet));
		}
		return null;
	}

	@Override
	public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
		for (PlusCalProcess proc : multiProcess.getProcesses()) {

			builder.defineGlobal(proc.getName().getName().getValue(), proc.getName().getUID());
			TLAScopeBuilder procTLAScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaBuilder.getDeclarations()), builder.getDefinitions(), builder.getReferences());
			proc.getName().getValue().accept(new TLAExpressionScopingVisitor(tlaBuilder, registry, loader, new HashSet<>()));
			Map<String, UID> procVars = new ChainMap<>(builder.getDeclarations());

			for (PlusCalVariableDeclaration var : proc.getVariables()) {
				if (procTLAScope.declare(var.getName().getValue(), var.getUID())) {
					procVars.put(var.getName().getValue(), var.getUID());
					registry.addLocalVariable(var.getUID());
				}
			}

			TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, procVars, new ChainMap<>(builder.getDefinitions()), builder.getReferences());
			procScope.defineLocal("self", proc.getName().getUID());
			registry.addLocalVariable(proc.getName().getUID());

			for (PlusCalLabeledStatements stmts : proc.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}

			for (PlusCalLabeledStatements stmts : proc.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, registry, loader, moduleRecursionSet));
			}
		}
		return null;
	}

}
