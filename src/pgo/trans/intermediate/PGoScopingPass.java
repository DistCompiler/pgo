package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.errors.TopLevelIssueContext;
import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.VariableDecl;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAUnit;
import pgo.modules.TLAModuleLoader;
import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PGoScopingPass {
	
	private PGoScopingPass() {}
	
	public static void perform(PGoTLAModule module, Algorithm algorithm, TLAModuleLoader loader){
		IssueContext ctx = new TopLevelIssueContext();
		DefinitionRegistryBuilder regBuilder = new DefinitionRegistryBuilder();
		TLAScopeBuilder tlaScope = new TLAScopeBuilder(ctx);
		
		PGoTLAUnitScopingVisitor.scopeModule(module, ctx, tlaScope, regBuilder, loader, new HashSet<>());
		
		TLAScopeBuilder pcalScope = tlaScope.makeNestedScope();
		
		for(VariableDecl decl : algorithm.getVariables()) {
			pcalScope.declare(decl.getName(), decl.getUID());
		}
		
		for(PGoTLAUnit unit : algorithm.getUnits()) {
			unit.accept(new PGoTLAUnitScopingVisitor(ctx, pcalScope, regBuilder, loader, new HashSet<>()));
		}
		
		algorithm.getProcesses().accept(new PlusCalProcessesScopingVisitor(ctx, pcalScope, tlaScope));
		
		for(Procedure proc : algorithm.getProcedures()) {
			
			pcalScope.defineGlobal(proc.getName(), proc.getUID());
			
			TLAScopeBuilder argScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(), pcalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());
			
			for(VariableDecl arg : proc.getArguments()) {
				arg.getValue().accept(new PGoTLAExpressionScopingVisitor(tlaScope));
				if(argScope.declare(arg.getName(), arg.getUID())) {
					args.put(arg.getName(), arg.getUID());
				}
			}
			// TODO: wait those aren't in the spec...
			/*for(VariableDecl arg : proc.getVariables()) {
				if(arg.getValue() != null) {
					arg.getValue().accept(new PGoTLAExpressionScopingVisitor(tlaScope));
				}
				procScope.declare(arg.getName(), arg.getUID());
			}*/
			
			TLAScopeBuilder procScope = new TLAScopeBuilder(ctx, args, new ChainMap<>(pcalScope.getDefinitions()), pcalScope.getReferences());
			
			for(LabeledStatements stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementLabelCaptureVisitor(ctx, procScope));
			}
			
			for(LabeledStatements stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope));
			}
		}
	}

}
