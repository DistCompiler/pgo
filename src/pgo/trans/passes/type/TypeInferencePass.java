package pgo.trans.passes.type;

import pgo.errors.IssueContext;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.PGoTypeGoTypeConversionVisitor;

import java.util.*;

public class TypeInferencePass {
	private TypeInferencePass() {}

	static void constrainVariableDeclaration(DefinitionRegistry registry, PlusCalVariableDeclaration var,
	                                         PGoTypeSolver solver, PGoTypeGenerator generator,
	                                         Map<UID, PGoTypeVariable> mapping) {
		PGoTypeVariable v;
		if (mapping.containsKey(var.getUID())) {
			v = mapping.get(var.getUID());
		} else {
			v = generator.get();
			mapping.put(var.getUID(), v);
		}

		PGoType valueType = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
				.wrappedVisit(var.getValue());
		if (var.isSet()) {
			PGoTypeVariable member = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, new PGoTypeSet(member, Collections.singletonList(valueType)), valueType));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, v, member));
		} else {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(var, v, valueType));
		}
	}

	public static Map<UID, PGoType> perform(IssueContext ctx, DefinitionRegistry registry,
	                                        ModularPlusCalBlock modularPlusCalBlock) {
		PGoTypeSolver solver = new PGoTypeSolver();
		PGoTypeGenerator generator = new PGoTypeGenerator("type");
		Map<UID, PGoTypeVariable> mapping = new HashMap<>();

		// make sure the user-provided constant values typecheck
		for (UID id : registry.getConstants()) {
			PGoTypeVariable fresh = generator.get();
			mapping.put(id, fresh);
			TLAExpression value = registry.getConstantValue(id);
			mapping.put(value.getUID(), fresh);
			PGoType type = value.accept(new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(value, fresh, type));
		}

		for (PlusCalVariableDeclaration var : modularPlusCalBlock.getVariables()) {
			constrainVariableDeclaration(registry, var, solver, generator, mapping);
		}

		for (TLAUnit unit : modularPlusCalBlock.getUnits()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}

		for (PlusCalProcedure p : modularPlusCalBlock.getProcedures()) {
			List<PGoType> paramTypes = new ArrayList<>();
			for (PlusCalVariableDeclaration var : p.getArguments()) {
				constrainVariableDeclaration(registry, var, solver, generator, mapping);
				paramTypes.add(mapping.get(var.getUID()));
			}
			PlusCalStatementTypeConstraintVisitor v =
					new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping);
			for (PlusCalStatement stmt : p.getBody()) {
				stmt.accept(v);
			}
			PGoTypeVariable fresh = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(p, fresh, new PGoTypeProcedure(paramTypes, Collections.singletonList(p))));
			mapping.put(p.getUID(), fresh);
		}

		modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesVisitor<Void, RuntimeException>(){
			@Override
			public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
				for (PlusCalStatement statements : singleProcess.getBody()) {
					statements.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
				}
				return null;
			}

			@Override
			public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
				for (PlusCalProcess process : multiProcess.getProcesses()) {
					constrainVariableDeclaration(registry, process.getName(), solver, generator, mapping);
					UID processVariableUID = process.getName().getUID();
					PGoType processVariableType = mapping.get(processVariableUID);
					solver.addConstraint(new PGoTypePolymorphicConstraint(process.getName().getUID(), Arrays.asList(
							Collections.singletonList(new PGoTypeEqualityConstraint(
									processVariableType,
									new PGoTypeInt(Collections.singletonList(process.getName())))),
							Collections.singletonList(new PGoTypeEqualityConstraint(
									processVariableType,
									new PGoTypeString(Collections.singletonList(process.getName())))))));
					for (PlusCalVariableDeclaration var : process.getVariables()) {
						constrainVariableDeclaration(registry, var, solver, generator, mapping);
					}
					for (PlusCalStatement statements : process.getBody()) {
						statements.accept(new PlusCalStatementTypeConstraintVisitor(ctx, registry, solver, generator, mapping));
					}
				}
				return null;
			}
		});

		solver.unify(ctx);
		if (ctx.hasErrors()) {
			return null;
		}
		Map<PGoTypeVariable, PGoType> typeMapping = solver.getMapping();

		Map<UID, PGoType> resultingTypeMapping = new HashMap<>();

		for (Map.Entry<UID, PGoTypeVariable> m : mapping.entrySet()) {
			UID uid = m.getKey();
			PGoType type = typeMapping.get(m.getValue());
			resultingTypeMapping.put(uid, type);
			if (type.containsVariables()) {
				ctx.error(new TypeInferenceFailureIssue(uid, type));
			}
		}

		for (UID varUID : registry.globalVariables()) {
			registry.updateGlobalVariableType(
					varUID, resultingTypeMapping.get(varUID).accept(new PGoTypeGoTypeConversionVisitor()));
		}

		return resultingTypeMapping;
	}
}
