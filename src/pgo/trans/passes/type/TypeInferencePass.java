package pgo.trans.passes.type;

import pgo.InternalCompilerError;
import pgo.errors.IssueContext;
import pgo.model.mpcal.*;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLARef;
import pgo.model.tla.TLAUnit;
import pgo.model.type.*;
import pgo.model.type.constraint.EqualityConstraint;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.model.type.constraint.PolymorphicConstraint;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.go.TypeConversionVisitor;
import pgo.util.Origin;

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

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			registry.addReadAndWrittenValueTypes(archetype, generator);
			UID selfVariableUID = archetype.getSelfVariableUID();
			mapping.put(selfVariableUID, generator.getTypeVariable(Collections.singletonList(archetype)));
			constrainSelfVariable(archetype, selfVariableUID, solver, mapping);
			List<Type> paramTypes = new ArrayList<>();
			Set<UID> paramUIDs = new HashSet<>();
			for (PlusCalVariableDeclaration declaration : archetype.getParams()) {
				paramUIDs.add(declaration.getUID());
				constrainVariableDeclaration(registry, declaration, solver, generator, mapping);
				paramTypes.add(mapping.get(declaration.getUID()));
			}
			for (PlusCalVariableDeclaration declaration : archetype.getVariables()) {
				constrainVariableDeclaration(registry, declaration, solver, generator, mapping);
			}
			for (PlusCalStatement statement : archetype.getBody()) {
				statement.accept(new ArchetypeBodyStatementTypeConstraintVisitor(
						registry, solver, generator, mapping, paramUIDs));
			}
			TypeVariable fresh = generator.getTypeVariable(Collections.singletonList(archetype));
			solver.addConstraint(new MonomorphicConstraint(
					archetype, fresh, new ProcedureType(paramTypes, Collections.singletonList(archetype))));
			mapping.put(archetype.getUID(), fresh);
		}

		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			constrainVariableDeclaration(registry, instance.getName(), solver, generator, mapping);
			UID selfVariableUID = instance.getName().getUID();
			constrainSelfVariable(instance, selfVariableUID, solver, mapping);
			ModularPlusCalArchetype target = registry.findArchetype(instance.getTarget());
			solver.addConstraint(new MonomorphicConstraint(
					instance, mapping.get(selfVariableUID), mapping.get(target.getSelfVariableUID())));
			List<Type> argumentTypes = new ArrayList<>();
			TLAExpressionTypeConstraintVisitor v =
					new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
			List<TLAExpression> arguments = instance.getArguments();
			for (TLAExpression expression : arguments) {
				argumentTypes.add(v.wrappedVisit(expression));
			}
			solver.addConstraint(new MonomorphicConstraint(
					instance,
					mapping.get(target.getUID()),
					new ProcedureType(argumentTypes, Collections.singletonList(instance))));
			Map<UID, UID> argsToParams = new HashMap<>();
			List<PlusCalVariableDeclaration> params = target.getParams();
			for (int i = 0; i < params.size(); i++) {
				TLAExpression argument = arguments.get(i);
				if (argument instanceof TLAGeneralIdentifier || argument instanceof TLARef) {
					argsToParams.put(registry.followReference(argument.getUID()), params.get(i).getUID());
				}
			}
			for (ModularPlusCalMapping instanceMapping : instance.getMappings()) {
				ModularPlusCalMappingVariable mappingVariable = instanceMapping.getVariable();
				if (mappingVariable.isFunctionCall() && argsToParams.containsKey(mappingVariable.getUID())) {
					UID declarationUID = argsToParams.get(mappingVariable.getUID());
					TypeVariable mapKeyType = generator.getTypeVariable(Collections.singletonList(declarationUID));
					solver.addConstraint(new PolymorphicConstraint(declarationUID, Arrays.asList(
							Arrays.asList(
									new EqualityConstraint(
											registry.getReadValueType(declarationUID),
											new SliceType(
													generator.getTypeVariable(
															Collections.singletonList(declarationUID)),
													Collections.singletonList(declarationUID))),
									new EqualityConstraint(
											registry.getWrittenValueType(declarationUID),
											new SliceType(
													generator.getTypeVariable(
															Collections.singletonList(declarationUID)),
													Collections.singletonList(declarationUID)))),
							Arrays.asList(
									new EqualityConstraint(
											registry.getReadValueType(declarationUID),
											new MapType(
													mapKeyType,
													generator.getTypeVariable(
															Collections.singletonList(declarationUID)),
													Collections.singletonList(declarationUID))),
									new EqualityConstraint(
											registry.getWrittenValueType(declarationUID),
											new MapType(
													mapKeyType,
													generator.getTypeVariable(
															Collections.singletonList(declarationUID)),
													Collections.singletonList(declarationUID)))),
							Arrays.asList(
									new EqualityConstraint(
											registry.getReadValueType(declarationUID),
											generator.getTypeVariable(Collections.singletonList(declarationUID))),
									new EqualityConstraint(
											registry.getWrittenValueType(declarationUID),
											generator.getTypeVariable(Collections.singletonList(declarationUID)))))));
				}
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

		TypeMapEntryProcessor processor = new TypeMapEntryProcessor();
		for (Map.Entry<UID, TypeVariable> m : mapping.entrySet()) {
			UID uid = m.getKey();
			TypeVariable typeVariable = m.getValue();
			resultingTypeMapping.put(uid, processor.process(substitution, typeVariable));
		}
		registry.forEachReadValueType(uid -> {
			TypeVariable typeVariable = (TypeVariable) registry.getReadValueType(uid);
			if (typeVariable == null) {
				throw new InternalCompilerError();
			}
			Type type = processor.process(substitution, typeVariable);
			registry.updateReadValueType(uid, type);
		});
		registry.forEachWrittenValueType(uid -> {
			TypeVariable typeVariable = (TypeVariable) registry.getWrittenValueType(uid);
			if (typeVariable == null) {
				throw new InternalCompilerError();
			}
			Type type = processor.process(substitution, typeVariable);
			registry.updateWrittenValueType(uid, type);
		});

		TypeConversionVisitor goTypeConversionVisitor = new TypeConversionVisitor();
		for (UID varUID : registry.globalVariables()) {
			registry.updateGlobalVariableType(
					varUID, resultingTypeMapping.get(varUID).accept(goTypeConversionVisitor));
		}

		return resultingTypeMapping;
	}
}
