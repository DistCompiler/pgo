package pgo.trans.passes.type;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.OperatorAccessor;
import pgo.trans.intermediate.TLABuiltins;

import java.util.*;
import java.util.stream.Collectors;

public class TLAExpressionTypeConstraintVisitor extends TLAExpressionVisitor<PGoType, RuntimeException> {
	protected final DefinitionRegistry registry;
	private final PGoTypeSolver solver;
	private final PGoTypeGenerator generator;
	private final Map<UID, PGoTypeVariable> mapping;

	public TLAExpressionTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver,
	                                          PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	private PGoType typeVariableReference(UID reference) {
		if (mapping.containsKey(reference)) {
			return mapping.get(reference);
		} else {
			PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(reference));
			mapping.put(reference, v);
			return v;
		}
	}

	public PGoType wrappedVisit(TLAExpression expr) {
		PGoType result = expr.accept(this);
		if (!mapping.containsKey(expr.getUID())) {
			PGoTypeVariable self = generator.getTypeVariable(Collections.singletonList(expr));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(expr, result, self));
			mapping.put(expr.getUID(), self);
		}
		return result;
	}

	private PGoType processQuantifierBound(TLAQuantifierBound qb) {
		PGoTypeVariable elementType = generator.getTypeVariable(Collections.singletonList(qb));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				qb, new PGoTypeSet(elementType, Collections.singletonList(qb)), wrappedVisit(qb.getSet())));
		switch(qb.getType()) {
			case IDS:
				for (TLAIdentifier id : qb.getIds()) {
					PGoTypeVariable idType = generator.getTypeVariable(Collections.singletonList(id));
					mapping.put(id.getUID(), idType);
					solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, elementType, idType));
				}
				break;
			case TUPLE:
				List<PGoType> tupleTypes = new ArrayList<>();
				for (TLAIdentifier id : qb.getIds()) {
					PGoTypeVariable idType = generator.getTypeVariable(Collections.singletonList(id));
					mapping.put(id.getUID(), idType);
					tupleTypes.add(idType);
				}
				solver.addConstraint(new PGoTypeMonomorphicConstraint(
						qb, elementType, new PGoTypeTuple(tupleTypes, Collections.singletonList(qb))));
				break;
			default:
				throw new Unreachable();
		}
		return elementType;
	}

	@Override
	public PGoType visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		PGoType fnType = wrappedVisit(tlaFunctionCall.getFunction());
		List<PGoType> paramTypes = new ArrayList<>();
		for (TLAExpression param : tlaFunctionCall.getParams()) {
			paramTypes.add(wrappedVisit(param));
		}
		PGoTypeVariable returnType = generator.getTypeVariable(Collections.singletonList(tlaFunctionCall));
		if (paramTypes.size() == 1) {
			solver.addConstraint(new PGoTypePolymorphicConstraint(tlaFunctionCall, Arrays.asList(
					Arrays.asList(
							new PGoTypeEqualityConstraint(
									fnType,
									new PGoTypeSlice(returnType, Collections.singletonList(tlaFunctionCall))),
							new PGoTypeEqualityConstraint(
									paramTypes.get(0),
									new PGoTypeInt(Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeMap(paramTypes.get(0), returnType, Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(tlaFunctionCall)))))));
		} else {
			solver.addConstraint(new PGoTypePolymorphicConstraint(tlaFunctionCall, Arrays.asList(
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeMap(
									new PGoTypeTuple(paramTypes, Collections.singletonList(tlaFunctionCall)),
									returnType,
									Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(tlaFunctionCall)))))));
		}
		return returnType;
	}

	@Override
	public PGoType visit(TLABinOp tlaBinOp) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(tlaBinOp.getOperation().getUID()))
				.constrainTypes(
						tlaBinOp.getOperation(), registry,
						Arrays.asList(wrappedVisit(tlaBinOp.getLHS()), wrappedVisit(tlaBinOp.getRHS())),
						solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLABool tlaBool) throws RuntimeException {
		return new PGoTypeBool(Collections.singletonList(tlaBool));
	}

	@Override
	public PGoType visit(TLACase tlaCase) throws RuntimeException {
		PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(tlaCase));
		for (TLACaseArm caseArm : tlaCase.getArms()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					tlaCase,
					wrappedVisit(caseArm.getCondition()),
					new PGoTypeBool(Collections.singletonList(caseArm.getCondition()))));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaCase, wrappedVisit(caseArm.getResult()), v));
		}

		if (tlaCase.getOther() != null) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaCase, wrappedVisit(tlaCase.getOther()), v));
		}

		return v;
	}

	@Override
	public PGoType visit(TLADot tlaDot) throws RuntimeException {
		PGoType fresh = generator.getTypeVariable(Collections.singletonList(tlaDot));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaDot, wrappedVisit(tlaDot.getExpression()), tlaDot.getField(), fresh));
		return fresh;
	}

	@Override
	public PGoType visit(TLAExistential tlaExistential) throws RuntimeException {
		for (TLAIdentifier id : tlaExistential.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.getTypeVariable(Collections.singletonList(id)));
		}
		wrappedVisit(tlaExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(tlaExistential));
	}

	@Override
	public PGoType visit(TLAFunction tlaFunction) throws RuntimeException {
		List<PGoType> keyTypes = new ArrayList<>();
		for (TLAQuantifierBound qb : tlaFunction.getArguments()) {
			keyTypes.add(processQuantifierBound(qb));
		}
		PGoType valueType = wrappedVisit(tlaFunction.getBody());
		PGoType fresh = generator.getTypeVariable(Collections.singletonList(tlaFunction));
		if (keyTypes.size() == 1) {
			solver.addConstraint(new PGoTypePolymorphicConstraint(tlaFunction, Arrays.asList(
					Arrays.asList(
							new PGoTypeEqualityConstraint(
									mapping.get(tlaFunction.getArguments().get(0).getSet().getUID()),
									new PGoTypeSet(
											generator.getTypeVariable(Collections.singletonList(tlaFunction)),
											Collections.singletonList(tlaFunction))),
							new PGoTypeEqualityConstraint(
									fresh,
									new PGoTypeMap(
											keyTypes.get(0),
											valueType,
											Collections.singletonList(tlaFunction)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fresh,
							new PGoTypeFunction(keyTypes, valueType, Collections.singletonList(tlaFunction)))))));
			return fresh;
		}
		if (keyTypes.size() > 1) {
			List<PGoTypeBasicConstraint> constraintsForMap = new ArrayList<>();
			for (TLAQuantifierBound arg : tlaFunction.getArguments()) {
				constraintsForMap.add(new PGoTypeEqualityConstraint(
						mapping.get(arg.getSet().getUID()),
						new PGoTypeSet(
								generator.getTypeVariable(Collections.singletonList(arg)),
								Collections.singletonList(tlaFunction))));
			}
			constraintsForMap.add(new PGoTypeEqualityConstraint(
					fresh,
					new PGoTypeMap(
							new PGoTypeTuple(keyTypes, Collections.singletonList(tlaFunction)),
							valueType,
							Collections.singletonList(tlaFunction))));
			solver.addConstraint(new PGoTypePolymorphicConstraint(tlaFunction, Arrays.asList(
					constraintsForMap,
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fresh,
							new PGoTypeFunction(
									keyTypes,
									valueType,
									Collections.singletonList(tlaFunction)))))));
			return fresh;
		}
		return new PGoTypeFunction(keyTypes, valueType, Collections.singletonList(tlaFunction));
	}

	@Override
	public PGoType visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		PGoType from = wrappedVisit(tlaFunctionSet.getFrom());
		PGoType to = wrappedVisit(tlaFunctionSet.getTo());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaFunctionSet,
				from,
				new PGoTypeSet(
						generator.getTypeVariable(Collections.singletonList(tlaFunctionSet.getFrom())),
						Collections.singletonList(tlaFunctionSet))));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaFunctionSet,
				to,
				new PGoTypeSet(
						generator.getTypeVariable(Collections.singletonList(tlaFunctionSet.getTo())),
						Collections.singletonList(tlaFunctionSet))));
		throw new TODO();
	}

	@Override
	public PGoType visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLAIf tlaIf) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaIf, wrappedVisit(tlaIf.getCond()), new PGoTypeBool(Collections.singletonList(tlaIf.getCond()))));
		PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(tlaIf));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaIf, wrappedVisit(tlaIf.getTval()), v));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaIf, wrappedVisit(tlaIf.getFval()), v));
		return v;
	}

	@Override
	public PGoType visit(TLALet tlaLet) throws RuntimeException {
		// TODO: let polymorphism
		for (TLAUnit unit : tlaLet.getDefinitions()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}
		return wrappedVisit(tlaLet.getBody());
	}

	@Override
	public PGoType visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaGeneralIdentifier.getUID()));
	}

	@Override
	public PGoType visit(TLATuple tlaTuple) throws RuntimeException {
		PGoType fresh = generator.getTypeVariable(Collections.singletonList(tlaTuple));
		PGoType elementType = generator.getTypeVariable(Collections.singletonList(tlaTuple));
		List<PGoType> contents = tlaTuple.getElements().stream()
				.map(this::wrappedVisit)
				.collect(Collectors.toList());
		List<PGoTypeBasicConstraint> commonConstraints = contents.stream()
				.map(t -> new PGoTypeEqualityConstraint(t, elementType))
				.collect(Collectors.toList());
		List<PGoTypeBasicConstraint> constraintsForChanType = new ArrayList<>(commonConstraints);
		constraintsForChanType.add(new PGoTypeEqualityConstraint(
				fresh,
				new PGoTypeChan(elementType, Collections.singletonList(tlaTuple))));
		List<PGoTypeBasicConstraint> constraintsForSliceType = new ArrayList<>(commonConstraints);
		constraintsForSliceType.add(new PGoTypeEqualityConstraint(
				fresh,
				new PGoTypeSlice(elementType, Collections.singletonList(tlaTuple))));
		solver.addConstraint(new PGoTypePolymorphicConstraint(tlaTuple, Arrays.asList(
				constraintsForSliceType,
				constraintsForChanType,
				Collections.singletonList(new PGoTypeEqualityConstraint(
						fresh,
						new PGoTypeTuple(contents, Collections.singletonList(tlaTuple)))))));
		return fresh;
	}

	@Override
	public PGoType visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLANumber tlaNumber) throws RuntimeException {
		// TODO this check should be more sophisticated
		if (tlaNumber.getVal().contains(".")) {
			return new PGoTypeReal(Collections.singletonList(tlaNumber));
		}
		return TLABuiltins.getPolymorphicNumberType(tlaNumber, solver, generator);
	}

	@Override
	public PGoType visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(tlaOperatorCall.getName().getUID()))
				.constrainTypes(
						tlaOperatorCall, registry,
						tlaOperatorCall.getArgs().stream()
								.map(this::wrappedVisit)
								.collect(Collectors.toList()),
						solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaQuantifiedExistential.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(tlaQuantifiedExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(tlaQuantifiedExistential));
	}

	@Override
	public PGoType visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaQuantifiedUniversal.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(tlaQuantifiedUniversal.getBody());
		return new PGoTypeBool(Collections.singletonList(tlaQuantifiedUniversal));
	}

	@Override
	public PGoType visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		List<PGoTypeConcreteRecord.Field> fields = new ArrayList<>();
		for (TLARecordConstructor.Field field : tlaRecordConstructor.getFields()) {
			fields.add(new PGoTypeConcreteRecord.Field(field.getName().getId(), wrappedVisit(field.getValue())));
		}
		return new PGoTypeConcreteRecord(fields, Collections.singletonList(tlaRecordConstructor));
	}

	@Override
	public PGoType visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		PGoTypeVariable elementType = generator.getTypeVariable(Collections.singletonList(tlaSetConstructor));
		for (TLAExpression element : tlaSetConstructor.getContents()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					tlaSetConstructor, elementType, wrappedVisit(element)));
		}
		return new PGoTypeSet(elementType, Collections.singletonList(tlaSetConstructor));
	}

	@Override
	public PGoType visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaSetComprehension.getBounds()) {
			processQuantifierBound(qb);
		}
		PGoType elementType = wrappedVisit(tlaSetComprehension.getBody());
		return new PGoTypeSet(elementType, Collections.singletonList(tlaSetComprehension));
	}

	@Override
	public PGoType visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		PGoType from = wrappedVisit(tlaSetRefinement.getFrom());
		PGoTypeVariable elementType = generator.getTypeVariable(Collections.singletonList(tlaSetRefinement));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaSetRefinement, from, new PGoTypeSet(elementType, Collections.singletonList(tlaSetRefinement))));
		if (tlaSetRefinement.getIdent().isTuple()) {
			List<PGoType> elements = new ArrayList<>();
			for (TLAIdentifier id : tlaSetRefinement.getIdent().getTuple()) {
				PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(id));
				mapping.put(id.getUID(), v);
				elements.add(v);
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(
					tlaSetRefinement,
					elementType,
					new PGoTypeTuple(elements, Collections.singletonList(tlaSetRefinement))));
		} else {
			TLAIdentifier id = tlaSetRefinement.getIdent().getId();
			mapping.put(id.getUID(), elementType);
		}
		PGoType condition = wrappedVisit(tlaSetRefinement.getWhen());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(
				tlaSetRefinement, condition, new PGoTypeBool(Collections.singletonList(tlaSetRefinement))));
		return new PGoTypeSet(elementType, Collections.singletonList(tlaSetRefinement));
	}

	@Override
	public PGoType visit(TLAString tlaString) throws RuntimeException {
		return new PGoTypeString(Collections.singletonList(tlaString));
	}

	@Override
	public PGoType visit(TLAUnary tlaUnary) throws RuntimeException {
		UID ref = registry.followReference(tlaUnary.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.constrainTypes(
				tlaUnary.getOperation(), registry,
				Collections.singletonList(wrappedVisit(tlaUnary.getOperand())),
				solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLAUniversal tlaUniversal) throws RuntimeException {
		for (TLAIdentifier id : tlaUniversal.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.getTypeVariable(Collections.singletonList(id)));
		}
		wrappedVisit(tlaUniversal.getBody());
		return new PGoTypeBool(Collections.singletonList(tlaUniversal));
	}

	@Override
	public PGoType visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		PGoTypeVariable v = generator.getTypeVariable(Collections.singletonList(plusCalDefaultInitValue));
		mapping.put(plusCalDefaultInitValue.getUID(), v);
		return v;
	}

	@Override
	public PGoType visit(TLAFairness fairness) throws RuntimeException{
		throw new InternalCompilerError();
	}

	@Override
	public PGoType visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaSpecialVariableVariable.getUID()));
	}

	@Override
	public PGoType visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaSpecialVariableValue.getUID()));
	}

	@Override
	public PGoType visit(TLARef tlaRef) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaRef.getUID()));
	}
}
