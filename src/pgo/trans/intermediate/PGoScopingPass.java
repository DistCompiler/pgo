package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import pgo.errors.IssueContext;
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
	
	public static DefinitionRegistry perform(IssueContext ctx, PGoTLAModule module, Algorithm algorithm, TLAModuleLoader loader){
		DefinitionRegistry regBuilder = new DefinitionRegistry();
		TLAScopeBuilder tlaScope = new TLAScopeBuilder(ctx, regBuilder.getReferences());
		
		TLAUnitScopingVisitor.scopeModule(module, ctx, tlaScope, regBuilder, loader, new HashSet<>());
		
		TLAScopeBuilder pcalScope = tlaScope.makeNestedScope();
		
		for(VariableDecl decl : algorithm.getVariables()) {
			pcalScope.declare(decl.getName(), decl.getUID());
		}
		
		for(PGoTLAUnit unit : algorithm.getUnits()) {
			unit.accept(new TLAUnitScopingVisitor(ctx, pcalScope, regBuilder, loader, new HashSet<>()));
		}
		
		algorithm.getProcesses().accept(
				new PlusCalProcessesScopingVisitor(ctx, pcalScope, tlaScope, regBuilder, loader, new HashSet<>()));
		
		for(Procedure proc : algorithm.getProcedures()) {
			
			pcalScope.defineGlobal(proc.getName(), proc.getUID());
			
			TLAScopeBuilder argScope = new TLAScopeBuilder(ctx, new ChainMap<>(tlaScope.getDeclarations()), new HashMap<>(), pcalScope.getReferences());
			Map<String, UID> args = new ChainMap<>(tlaScope.getDeclarations());
			
			for(VariableDecl arg : proc.getArguments()) {
				arg.getValue().accept(new TLAExpressionScopingVisitor(tlaScope, regBuilder, loader, new HashSet<>()));
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
				stmts.accept(new PlusCalStatementScopingVisitor(ctx, procScope, regBuilder, loader, new HashSet<>()));
			}
		}
		
		return regBuilder;
	}

}
