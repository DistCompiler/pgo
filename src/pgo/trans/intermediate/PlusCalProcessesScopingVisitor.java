package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.pcal.VariableDecl;
import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PlusCalProcessesScopingVisitor extends ProcessesVisitor<Void, RuntimeException> {

	private IssueContext ctx;
	private TLAScopeBuilder builder;
	private TLAScopeBuilder tlaBuilder;
	
	public PlusCalProcessesScopingVisitor(IssueContext ctx, TLAScopeBuilder builder, TLAScopeBuilder tlaBuilder) {
		this.ctx = ctx;
		this.builder = builder;
		this.tlaBuilder = tlaBuilder;
	}
	
	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		TLAScopeBuilder labelScope = new TLAScopeBuilder(ctx, new HashMap<>(), new ChainMap<>(builder.getDefinitions()), builder.getReferences());
		
		for(LabeledStatements stmts : singleProcess.getLabeledStatements()) {
			stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, labelScope));
		}
		
		TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, builder.getDeclarations(), labelScope.getDefinitions(), builder.getReferences());
		for(LabeledStatements stmts : singleProcess.getLabeledStatements()) {
			stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope));
		}
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		for(PcalProcess proc : multiProcess.getProcesses()) {
			
			builder.defineGlobal(proc.getName().getName(), proc.getName().getUID());
			TLAScopeBuilder procTLAScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaBuilder.getDeclarations()), builder.getDefinitions(), builder.getReferences());
			Map<String, UID> procVars = new ChainMap<>(builder.getDeclarations());
			
			for(VariableDecl var : proc.getVariables()) {
				if(procTLAScope.declare(var.getName(), var.getUID())) {
					procVars.put(var.getName(), var.getUID());
				}
			}
			
			TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, procVars, new ChainMap<>(builder.getDefinitions()), builder.getReferences());
			
			for(LabeledStatements stmts : proc.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}
			
			for(LabeledStatements stmts : proc.getLabeledStatements()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope));
			}
		}
		return null;
	}

}
