package pgo.trans.passes.type;

import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAUnit;
import pgo.model.type.*;
import pgo.model.type.constraint.EqualityConstraint;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.model.type.constraint.PolymorphicConstraint;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.go.TypeConversionVisitor;
import pgo.util.Origin;
import pgo.util.UnionFind;

import java.util.*;

public class TypeInferencePass {
	private TypeInferencePass() {}

	static void constrainVariableDeclaration(DefinitionRegistry registry, PlusCalVariableDeclaration var,
	                                         TypeSolver solver, TypeGenerator generator,
	                                         Map<UID, TypeVariable> mapping) {
		TypeVariable v;
		if (mapping.containsKey(var.getUID())) {
			v = mapping.get(var.getUID());
		} else {
			v = generator.getTypeVariable(Collections.singletonList(var));
			mapping.put(var.getUID(), v);
		}

		Type valueType = new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping)
				.wrappedVisit(var.getValue());
		if (var.isSet()) {
			TypeVariable member = generator.getTypeVariable(Collections.singletonList(valueType));
			solver.addConstraint(new MonomorphicConstraint(
					var, new SetType(member, Collections.singletonList(valueType)), valueType));
			solver.addConstraint(new MonomorphicConstraint(var, v, member));
		} else {
			solver.addConstraint(new MonomorphicConstraint(var, v, valueType));
		}
	}

	private static void constrainSelfVariable(Origin origin, UID selfVariableUID, TypeSolver solver,
	                                          Map<UID, TypeVariable> mapping) {
		Type selfVariableType = mapping.get(selfVariableUID);
		solver.addConstraint(new PolymorphicConstraint(selfVariableUID, Arrays.asList(
				Collections.singletonList(new EqualityConstraint(
						selfVariableType,
						new IntType(Collections.singletonList(origin)))),
				Collections.singletonList(new EqualityConstraint(
						selfVariableType,
						new StringType(Collections.singletonList(origin)))))));
	}

	public static Map<UID, Type> perform(IssueContext ctx, DefinitionRegistry registry,
	                                     ModularPlusCalBlock modularPlusCalBlock) {
		TypeSolver solver = new TypeSolver();
		TypeGenerator generator = new TypeGenerator("type");
		Map<UID, TypeVariable> mapping = new HashMap<>();

		// make sure the user-provided constant values typecheck
		for (UID id : registry.getConstants()) {
			TypeVariable fresh = generator.getTypeVariable(Collections.singletonList(id));
			mapping.put(id, fresh);
			registry.getConstantValue(id).ifPresent(value -> {
				mapping.put(value.getUID(), fresh);
				Type type = value.accept(new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping));
				solver.addConstraint(new MonomorphicConstraint(value, fresh, type));
			});
		}

		for (PlusCalVariableDeclaration var : modularPlusCalBlock.getVariables()) {
			constrainVariableDeclaration(registry, var, solver, generator, mapping);
		}

		for (TLAUnit unit : modularPlusCalBlock.getUnits()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}

		for (PlusCalProcedure p : modularPlusCalBlock.getProcedures()) {
			List<Type> paramTypes = new ArrayList<>();
			for (PlusCalVariableDeclaration var : p.getParams()) {
				constrainVariableDeclaration(registry, var, solver, generator, mapping);
				paramTypes.add(mapping.get(var.getUID()));
			}
			for (PlusCalVariableDeclaration declaration : p.getVariables()) {
				constrainVariableDeclaration(registry, declaration, solver, generator, mapping);
			}
			PlusCalStatementTypeConstraintVisitor v =
					new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping);
			for (PlusCalStatement stmt : p.getBody()) {
				stmt.accept(v);
			}
			TypeVariable fresh = generator.getTypeVariable(Collections.singletonList(p));
			solver.addConstraint(new MonomorphicConstraint(
					p, fresh, new ProcedureType(paramTypes, Collections.singletonList(p))));
			mapping.put(p.getUID(), fresh);
		}

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getInstantiatedArchetypes()) {
			boolean[] signature = registry.getSignature(archetype.getUID())
					.orElseGet(() -> new boolean[archetype.getParams().size()]);
			List<PlusCalVariableDeclaration> params = archetype.getParams();
			Set<UID> paramUIDs = new HashSet<>();
			Set<UID> functionMappedParamUIDs = new HashSet<>();
			for (int i = 0; i < params.size(); i++) {
				PlusCalVariableDeclaration param = params.get(i);
				TypeVariable fresh = generator.getTypeVariable(Collections.singletonList(param));
				mapping.put(param.getUID(), fresh);
				paramUIDs.add(param.getUID());
				if (signature[i]) {
					solver.addConstraint(new MonomorphicConstraint(param, fresh, new ArchetypeResourceCollectionType(
							generator.getTypeVariable(Collections.singletonList(param)),
							generator.getTypeVariable(Collections.singletonList(param)),
							generator.getTypeVariable(Collections.singletonList(param)),
							Collections.singletonList(param))));
					functionMappedParamUIDs.add(param.getUID());
				} else {
					solver.addConstraint(new MonomorphicConstraint(param, fresh, new ArchetypeResourceType(
							generator.getTypeVariable(Collections.singletonList(param)),
							generator.getTypeVariable(Collections.singletonList(param)),
							Collections.singletonList(param))));
				}
			}
			UID selfVariableUID = archetype.getSelfVariableUID();
			mapping.put(selfVariableUID, generator.getTypeVariable(Collections.singletonList(archetype)));
			constrainSelfVariable(archetype, selfVariableUID, solver, mapping);
			for (PlusCalVariableDeclaration declaration : archetype.getVariables()) {
				constrainVariableDeclaration(registry, declaration, solver, generator, mapping);
			}
			for (PlusCalStatement statement : archetype.getBody()) {
				statement.accept(new ArchetypeBodyStatementTypeConstraintVisitor(
						registry, solver, generator, mapping, functionMappedParamUIDs, paramUIDs));
			}
		}

		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			constrainVariableDeclaration(registry, instance.getName(), solver, generator, mapping);
			UID selfVariableUID = instance.getName().getUID();
			constrainSelfVariable(instance, selfVariableUID, solver, mapping);
			ModularPlusCalArchetype target = registry.findArchetype(instance.getTarget());
			solver.addConstraint(new MonomorphicConstraint(
					instance, mapping.get(selfVariableUID), mapping.get(target.getSelfVariableUID())));
			TLAExpressionTypeConstraintVisitor v =
					new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
			for (TLAExpression expression : instance.getArguments()) {
				v.wrappedVisit(expression);
			}
		}

		modularPlusCalBlock.getProcesses().accept(new PlusCalProcessesVisitor<Void, RuntimeException>(){
			@Override
			public Void visit(PlusCalSingleProcess singleProcess) throws RuntimeException {
				for (PlusCalStatement statements : singleProcess.getBody()) {
					statements.accept(new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping));
				}
				return null;
			}

			@Override
			public Void visit(PlusCalMultiProcess multiProcess) throws RuntimeException {
				for (PlusCalProcess process : multiProcess.getProcesses()) {
					constrainVariableDeclaration(registry, process.getName(), solver, generator, mapping);
					constrainSelfVariable(process, process.getName().getUID(), solver, mapping);
					for (PlusCalVariableDeclaration var : process.getVariables()) {
						constrainVariableDeclaration(registry, var, solver, generator, mapping);
					}
					for (PlusCalStatement statements : process.getBody()) {
						statements.accept(
								new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping));
					}
				}
				return null;
			}
		});

		solver.unify(ctx);
		if (ctx.hasErrors()) {
			return Collections.emptyMap();
		}
		TypeSubstitution substitution = solver.getSubstitution();

		Map<UID, Type> resultingTypeMapping = new HashMap<>();

		Set<TypeVariable> unresolvedVariables = new HashSet<>();
		Map<TypeVariable, Type> additionalMappings = new HashMap<>();
		TypeVariableCollectionVisitor collector = new TypeVariableCollectionVisitor(unresolvedVariables);
		TypeVariableSubstitutionVisitor subs =
				new TypeVariableSubstitutionVisitor(new TypeSubstitution(new UnionFind<>(), additionalMappings));
		InterfaceType pGoInterfaceType = new InterfaceType(Collections.emptyList());
		for (Map.Entry<UID, TypeVariable> m : mapping.entrySet()) {
			UID uid = m.getKey();
			TypeVariable typeVariable = m.getValue();
			Type type;
			if (substitution.containsKey(typeVariable)) {
				type = substitution.get(typeVariable);
			} else {
				type = pGoInterfaceType;
				additionalMappings.put(typeVariable, pGoInterfaceType);
			}
			type.accept(collector);
			for (TypeVariable unresolvedVariable : unresolvedVariables) {
				additionalMappings.put(unresolvedVariable, pGoInterfaceType);
			}
			unresolvedVariables.clear();
			resultingTypeMapping.put(uid, type.accept(subs));
		}

		TypeConversionVisitor goTypeConversionVisitor = new TypeConversionVisitor();
		for (UID varUID : registry.globalVariables()) {
			registry.updateGlobalVariableType(
					varUID, resultingTypeMapping.get(varUID).accept(goTypeConversionVisitor));
		}

		return resultingTypeMapping;
	}
}
