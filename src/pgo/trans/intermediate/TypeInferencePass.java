package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.model.pcal.Algorithm;
import pgo.model.pcal.LabeledStatements;
import pgo.model.pcal.MultiProcess;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.ProcessesVisitor;
import pgo.model.pcal.SingleProcess;
import pgo.model.pcal.Statement;
import pgo.model.pcal.VariableDecl;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class TypeInferencePass {
	
	private TypeInferencePass() {}
	
	public static void constrainVariableDecl(DefinitionRegistry registry, VariableDecl var, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		PGoTypeVariable v;
		if(mapping.containsKey(var.getUID())) {
			v = mapping.get(var.getUID());
		}else {
			v = generator.get();
			mapping.put(var.getUID(), v);
		}
		
		PGoType valueType = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
				.wrappedVisit(var.getValue());
		if(var.isSet()) {
			PGoTypeVariable member = generator.get();
			solver.accept(new PGoTypeConstraint(new PGoTypeSet(member), valueType));
			solver.accept(new PGoTypeConstraint(v, member));
		}else {
			solver.accept(new PGoTypeConstraint(v, valueType));
		}
	}
	
	public static Map<UID, PGoType> perform(DefinitionRegistry registry, Algorithm pcal) {
		
		PGoTypeSolver solver = new PGoTypeSolver();
		PGoTypeGenerator generator = new PGoTypeGenerator("type");
		Map<UID, PGoTypeVariable> mapping = new HashMap<>();
		
		for(VariableDecl var : pcal.getVariables()) {
			constrainVariableDecl(registry, var, solver, generator, mapping);
		}
		
		for(PGoTLAUnit unit : pcal.getUnits()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}
		
		pcal.getProcesses().accept(new ProcessesVisitor<Void, RuntimeException>(){

			@Override
			public Void visit(SingleProcess singleProcess) throws RuntimeException {
				for(LabeledStatements stmts : singleProcess.getLabeledStatements()) {
					for(Statement stmt : stmts.getStatements()) {
						stmt.accept(new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping));
					}
				}
				return null;
			}

			@Override
			public Void visit(MultiProcess multiProcess) throws RuntimeException {
				for(PcalProcess proc : multiProcess.getProcesses()) {
					for(VariableDecl var : proc.getVariables()) {
						constrainVariableDecl(registry, var, solver, generator, mapping);
					}
					constrainVariableDecl(registry, proc.getName(), solver, generator, mapping);
					for(LabeledStatements stmts : proc.getLabeledStatements()) {
						for(Statement stmt : stmts.getStatements()) {
							stmt.accept(new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping));
						}
					}
				}
				return null;
			}
			
		});
		
		solver.unify();
		Map<PGoTypeVariable, PGoType> typeMapping = solver.getMapping();
		
		Map<UID, PGoType> resultingTypeMapping = new HashMap<>();
		
		for(Map.Entry<UID, PGoTypeVariable> m : mapping.entrySet()) {
			resultingTypeMapping.put(m.getKey(), typeMapping.get(m.getValue()));
		}
		
		System.out.println(resultingTypeMapping);
		
		return resultingTypeMapping;
	}

}
