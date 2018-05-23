package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import pgo.errors.IssueContext;
import pgo.model.pcal.*;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.type.*;
import pgo.scope.UID;

public class TypeInferencePass {

	private TypeInferencePass() {}

	static void constrainVariableDecl(IssueContext ctx, DefinitionRegistry registry, VariableDecl var, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		PGoTypeVariable v;
		if(mapping.containsKey(var.getUID())) {
			v = mapping.get(var.getUID());
		}else {
			v = generator.get();
			mapping.put(var.getUID(), v);
		}

		PGoType valueType = new TLAExpressionTypeConstraintVisitor(ctx, registry, solver, generator, mapping)
				.wrappedVisit(var.getValue());
		if(var.isSet()) {
			PGoTypeVariable member = generator.get();
			solver.addConstraint(ctx, new PGoTypeConstraint(var, new PGoTypeSet(member), valueType));
			solver.addConstraint(ctx, new PGoTypeConstraint(var, v, member));
		}else {
			solver.addConstraint(ctx, new PGoTypeConstraint(var, v, valueType));
		}
	}

	public static Map<UID, PGoType> perform(IssueContext ctx, DefinitionRegistry registry, Algorithm pcal) {

		PGoTypeSolver solver = new PGoTypeSolver();
		PGoTypeGenerator generator = new PGoTypeGenerator("type");
		Map<UID, PGoTypeVariable> mapping = new HashMap<>();

		for (VariableDecl var : pcal.getVariables()) {
			constrainVariableDecl(ctx, registry, var, solver, generator, mapping);
		}

		for (PGoTLAUnit unit : pcal.getUnits()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}

		for (Procedure p : pcal.getProcedures()) {
			List<PGoType> paramTypes = new ArrayList<>();
			for (VariableDecl var : p.getArguments()) {
				constrainVariableDecl(ctx, registry, var, solver, generator, mapping);
				paramTypes.add(mapping.get(var.getUID()));
			}
			PlusCalStatementTypeConstraintVisitor v =
					new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping);
			for (Statement stmt : p.getBody()) {
				stmt.accept(v);
			}
			PGoTypeVariable fresh = generator.get();
			solver.addConstraint(ctx, new PGoTypeConstraint(p, fresh, new PGoTypeFunction(paramTypes, PGoTypeVoid.getInstance())));
			mapping.put(p.getUID(), fresh);
		}

		pcal.getProcesses().accept(new ProcessesVisitor<Void, RuntimeException>(){

			@Override
			public Void visit(SingleProcess singleProcess) throws RuntimeException {
				for (LabeledStatements stmts : singleProcess.getLabeledStatements()) {
					for (Statement stmt : stmts.getStatements()) {
						stmt.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
					}
				}
				return null;
			}

			@Override
			public Void visit(MultiProcess multiProcess) throws RuntimeException {
				for (PcalProcess proc : multiProcess.getProcesses()) {
					for (VariableDecl var : proc.getVariables()) {
						constrainVariableDecl(ctx, registry, var, solver, generator, mapping);
					}
					constrainVariableDecl(ctx, registry, proc.getName(), solver, generator, mapping);
					for (LabeledStatements stmts : proc.getLabeledStatements()) {
						for (Statement stmt : stmts.getStatements()) {
							stmt.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
						}
					}
				}
				return null;
			}

		});

		solver.simplify(ctx);
		if (ctx.hasErrors()) {
			return null;
		}
		Map<PGoTypeVariable, PGoType> typeMapping = solver.getMapping();

		Map<UID, PGoType> resultingTypeMapping = new HashMap<>();

		for (Map.Entry<UID, PGoTypeVariable> m : mapping.entrySet()) {
			resultingTypeMapping.put(m.getKey(), typeMapping.get(m.getValue()));
		}

		System.out.println(resultingTypeMapping);

		return resultingTypeMapping;
	}

}
