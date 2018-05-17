package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.Procedure;
import pgo.model.pcal.VariableDecl;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAUnit;
import pgo.scope.UID;

public class PGoScopingPass {
	
	private PGoScopingPass() {}
	
	TLAModuleScope findTLAModuleScope(PGoTLAModule module, Algorithm algorithm){
		// TODO: look up extended modules
		Map<String, UID> declarations = new HashMap<>();
		Map<QualifiedName, UID> definitions = new HashMap<>();
		Map<UID, UID> references = new HashMap<>();
		
		List<ScopeConflict> conflicts = new ArrayList<>();
		List<UID> danglingReferences = new ArrayList<>();
		
		ScopeInfoBuilder scope = new ScopeInfoBuilder(declarations, definitions, conflicts, references, danglingReferences);
		for(PGoTLAUnit unit : module.getPreTranslationUnits()) {
			unit.accept(new PGoTLAUnitScopingVisitor(scope));
		}
		
		Map<String, UID> globalVariables = new HashMap<>();
		PlusCalScopeBuilder pcalScope = new PlusCalScopeBuilder(declarations, definitions, globalVariables, references, danglingReferences, conflicts);
		
		for(VariableDecl decl : algorithm.getVariables()) {
			pcalScope.declare(decl.getName(), decl.getUID());
		}
		algorithm.getProcesses().accept(new PlusCalProcessesScopingVisitor(pcalScope));
		
		for(Procedure proc : algorithm.getProcedures()) {
			PlusCalScopeBuilder procScope = pcalScope.makeNestedScope();
			for(VariableDecl arg : proc.getArguments()) {
				arg.getValue().accept(new PGoTLAExpressionScopingVisitor(scope));
				procScope.declare(arg.getName(), arg.getUID());
			}
			for(VariableDecl arg : proc.getVariables()) {
				if(arg.getValue() != null) {
					arg.getValue().accept(new PGoTLAExpressionScopingVisitor(scope));
				}
				procScope.declare(arg.getName(), arg.getUID());
			}
			for(LabeledStatements stmts : proc.getBody()) {
				stmts.accept(new PlusCalStatementScopingVisitor(procScope));
			}
		}
		return null;
	}

}
