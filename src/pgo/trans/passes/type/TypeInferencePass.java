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
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.go.PGoTypeGoTypeConversionVisitor;
import pgo.util.Origin;

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

	private static void constrainSelfVariable(Origin origin, UID selfVariableUID, PGoTypeSolver solver,
	                                          Map<UID, PGoTypeVariable> mapping) {
		PGoType selfVariableType = mapping.get(selfVariableUID);
		solver.addConstraint(new PGoTypePolymorphicConstraint(selfVariableUID, Arrays.asList(
				Collections.singletonList(new PGoTypeEqualityConstraint(
						selfVariableType,
						new PGoTypeInt(Collections.singletonList(origin)))),
				Collections.singletonList(new PGoTypeEqualityConstraint(
						selfVariableType,
						new PGoTypeString(Collections.singletonList(origin)))))));
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
			for (PlusCalVariableDeclaration var : p.getParams()) {
				constrainVariableDeclaration(registry, var, solver, generator, mapping);
				paramTypes.add(mapping.get(var.getUID()));
			}
			PlusCalStatementTypeConstraintVisitor v =
					new PlusCalStatementTypeConstraintVisitor(registry, solver, generator, mapping);
			for (PlusCalStatement stmt : p.getBody()) {
				stmt.accept(v);
			}
			PGoTypeVariable fresh = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(p, fresh, new PGoTypeProcedure(paramTypes, Collections.singletonList(p))));
			mapping.put(p.getUID(), fresh);
		}

		for (ModularPlusCalArchetype archetype : modularPlusCalBlock.getArchetypes()) {
			registry.addReadAndWrittenValueTypes(archetype, generator);
			UID selfVariableUID = archetype.getSelfVariableUID();
			mapping.put(selfVariableUID, generator.get());
			constrainSelfVariable(archetype, selfVariableUID, solver, mapping);
			List<PGoType> paramTypes = new ArrayList<>();
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
			PGoTypeVariable fresh = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					archetype, fresh, new PGoTypeProcedure(paramTypes, Collections.singletonList(archetype))));
			mapping.put(archetype.getUID(), fresh);
		}

		for (ModularPlusCalInstance instance : modularPlusCalBlock.getInstances()) {
			constrainVariableDeclaration(registry, instance.getName(), solver, generator, mapping);
			UID selfVariableUID = instance.getName().getUID();
			constrainSelfVariable(instance, selfVariableUID, solver, mapping);
			ModularPlusCalArchetype target = registry.findArchetype(instance.getTarget());
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					instance, mapping.get(selfVariableUID), mapping.get(target.getSelfVariableUID())));
			List<PGoType> argumentTypes = new ArrayList<>();
			TLAExpressionTypeConstraintVisitor v =
					new TLAExpressionTypeConstraintVisitor(registry, solver, generator, mapping);
			List<TLAExpression> arguments = instance.getArguments();
			for (TLAExpression expression : arguments) {
				argumentTypes.add(v.wrappedVisit(expression));
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					instance,
					mapping.get(target.getUID()),
					new PGoTypeProcedure(argumentTypes, Collections.singletonList(instance))));
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
				if (mappingVariable.isFunctionCalls() && argsToParams.containsKey(mappingVariable.getUID())) {
					UID declarationUID = argsToParams.get(mappingVariable.getUID());
					PGoTypeVariable mapKeyType = generator.get();
					solver.addConstraint(new PGoTypePolymorphicConstraint(declarationUID, Arrays.asList(
							Arrays.asList(
									new PGoTypeEqualityConstraint(
											registry.getReadValueType(declarationUID),
											new PGoTypeSlice(
													generator.get(),
													Collections.singletonList(declarationUID))),
									new PGoTypeEqualityConstraint(
											registry.getWrittenValueType(declarationUID),
											new PGoTypeSlice(
													generator.get(),
													Collections.singletonList(declarationUID)))),
							Arrays.asList(
									new PGoTypeEqualityConstraint(
											registry.getReadValueType(declarationUID),
											new PGoTypeMap(
													mapKeyType,
													generator.get(),
													Collections.singletonList(declarationUID))),
									new PGoTypeEqualityConstraint(
											registry.getWrittenValueType(declarationUID),
											new PGoTypeMap(
													mapKeyType,
													generator.get(),
													Collections.singletonList(declarationUID)))),
							Arrays.asList(
									new PGoTypeEqualityConstraint(
											registry.getReadValueType(declarationUID), generator.get()),
									new PGoTypeEqualityConstraint(
											registry.getWrittenValueType(declarationUID), generator.get())))));
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
			return null;
		}
		Map<PGoTypeVariable, PGoType> typeMapping = solver.getMapping();

		Map<UID, PGoType> resultingTypeMapping = new HashMap<>();

		TypeMapEntryProcessor processor = new TypeMapEntryProcessor();
		for (Map.Entry<UID, PGoTypeVariable> m : mapping.entrySet()) {
			UID uid = m.getKey();
			PGoTypeVariable typeVariable = m.getValue();
			resultingTypeMapping.put(uid, processor.process(typeMapping, uid, typeVariable));
		}
		registry.forEachReadValueType(uid -> {
			PGoTypeVariable typeVariable = (PGoTypeVariable) registry.getReadValueType(uid);
			if (typeVariable == null) {
				throw new InternalCompilerError();
			}
			PGoType type = processor.process(typeMapping, uid, typeVariable);
			registry.updateReadValueType(uid, type);
		});
		registry.forEachWrittenValueType(uid -> {
			PGoTypeVariable typeVariable = (PGoTypeVariable) registry.getWrittenValueType(uid);
			if (typeVariable == null) {
				throw new InternalCompilerError();
			}
			PGoType type = processor.process(typeMapping, uid, typeVariable);
			registry.updateWrittenValueType(uid, type);
		});

		PGoTypeGoTypeConversionVisitor goTypeConversionVisitor = new PGoTypeGoTypeConversionVisitor();
		for (UID varUID : registry.globalVariables()) {
			registry.updateGlobalVariableType(
					varUID, resultingTypeMapping.get(varUID).accept(goTypeConversionVisitor));
		}

		return resultingTypeMapping;
	}
}
