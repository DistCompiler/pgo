package pgo.trans.passes.type;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.model.type.constraint.BasicConstraint;
import pgo.model.type.constraint.EqualityConstraint;
import pgo.model.type.constraint.MonomorphicConstraint;
import pgo.model.type.constraint.PolymorphicConstraint;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.OperatorAccessor;
import pgo.trans.intermediate.TLABuiltins;

import java.util.*;
import java.util.stream.Collectors;

public class TLAExpressionTypeConstraintVisitor extends TLAExpressionVisitor<Type, RuntimeException> {
	protected final DefinitionRegistry registry;
	private final TypeSolver solver;
	private final TypeGenerator generator;
	private final Map<UID, TypeVariable> mapping;

	public TLAExpressionTypeConstraintVisitor(DefinitionRegistry registry, TypeSolver solver,
	                                          TypeGenerator generator, Map<UID, TypeVariable> mapping) {
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	private Type typeVariableReference(UID reference) {
		if (mapping.containsKey(reference)) {
			return mapping.get(reference);
		} else {
			TypeVariable v = generator.getTypeVariable(Collections.singletonList(reference));
			mapping.put(reference, v);
			return v;
		}
	}

	public Type wrappedVisit(TLAExpression expr) {
		Type result = expr.accept(this);
		if (!mapping.containsKey(expr.getUID())) {
			TypeVariable self = generator.getTypeVariable(Collections.singletonList(expr));
			solver.addConstraint(new MonomorphicConstraint(expr, result, self));
			mapping.put(expr.getUID(), self);
		}
		return result;
	}

	private Type processQuantifierBound(TLAQuantifierBound qb) {
		TypeVariable elementType = generator.getTypeVariable(Collections.singletonList(qb));
		solver.addConstraint(new MonomorphicConstraint(
				qb, new SetType(elementType, Collections.singletonList(qb)), wrappedVisit(qb.getSet())));
		switch(qb.getType()) {
			case IDS:
				for (TLAIdentifier id : qb.getIds()) {
					TypeVariable idType = generator.getTypeVariable(Collections.singletonList(id));
					mapping.put(id.getUID(), idType);
					solver.addConstraint(new MonomorphicConstraint(qb, elementType, idType));
				}
				break;
			case TUPLE:
				List<Type> tupleTypes = new ArrayList<>();
				for (TLAIdentifier id : qb.getIds()) {
					TypeVariable idType = generator.getTypeVariable(Collections.singletonList(id));
					mapping.put(id.getUID(), idType);
					tupleTypes.add(idType);
				}
				solver.addConstraint(new MonomorphicConstraint(
						qb, elementType, new TupleType(tupleTypes, Collections.singletonList(qb))));
				break;
			default:
				throw new Unreachable();
		}
		return elementType;
	}

	@Override
	public Type visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		Type fnType = wrappedVisit(tlaFunctionCall.getFunction());
		List<Type> paramTypes = new ArrayList<>();
		for (TLAExpression param : tlaFunctionCall.getParams()) {
			paramTypes.add(wrappedVisit(param));
		}
		TypeVariable returnType = generator.getTypeVariable(Collections.singletonList(tlaFunctionCall));
		if (paramTypes.size() == 1) {
			solver.addConstraint(new PolymorphicConstraint(tlaFunctionCall, Arrays.asList(
					Arrays.asList(
							new EqualityConstraint(
									fnType,
									new SliceType(returnType, Collections.singletonList(tlaFunctionCall))),
							new EqualityConstraint(
									paramTypes.get(0),
									new IntType(Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new EqualityConstraint(
							fnType,
							new MapType(paramTypes.get(0), returnType, Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new EqualityConstraint(
							fnType,
							new FunctionType(paramTypes, returnType, Collections.singletonList(tlaFunctionCall)))))));
		} else {
			solver.addConstraint(new PolymorphicConstraint(tlaFunctionCall, Arrays.asList(
					Collections.singletonList(new EqualityConstraint(
							fnType,
							new MapType(
									new TupleType(paramTypes, Collections.singletonList(tlaFunctionCall)),
									returnType,
									Collections.singletonList(tlaFunctionCall)))),
					Collections.singletonList(new EqualityConstraint(
							fnType,
							new FunctionType(paramTypes, returnType, Collections.singletonList(tlaFunctionCall)))))));
		}
		return returnType;
	}

	@Override
	public Type visit(TLABinOp tlaBinOp) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(tlaBinOp.getOperation().getUID()))
				.constrainTypes(
						tlaBinOp.getOperation(), registry,
						Arrays.asList(wrappedVisit(tlaBinOp.getLHS()), wrappedVisit(tlaBinOp.getRHS())),
						solver, generator, mapping);
	}

	@Override
	public Type visit(TLABool tlaBool) throws RuntimeException {
		return new BoolType(Collections.singletonList(tlaBool));
	}

	@Override
	public Type visit(TLACase tlaCase) throws RuntimeException {
		TypeVariable v = generator.getTypeVariable(Collections.singletonList(tlaCase));
		for (TLACaseArm caseArm : tlaCase.getArms()) {
			solver.addConstraint(new MonomorphicConstraint(
					tlaCase,
					wrappedVisit(caseArm.getCondition()),
					new BoolType(Collections.singletonList(caseArm.getCondition()))));
			solver.addConstraint(new MonomorphicConstraint(tlaCase, wrappedVisit(caseArm.getResult()), v));
		}

		if (tlaCase.getOther() != null) {
			solver.addConstraint(new MonomorphicConstraint(tlaCase, wrappedVisit(tlaCase.getOther()), v));
		}

		return v;
	}

	@Override
	public Type visit(TLADot tlaDot) throws RuntimeException {
		Type fresh = generator.getTypeVariable(Collections.singletonList(tlaDot));
		AbstractRecordType abstractRecord = generator.getAbstractRecord(Collections.singletonList(tlaDot));
		solver.addConstraint(
				new MonomorphicConstraint(tlaDot, abstractRecord, wrappedVisit(tlaDot.getExpression())));
		solver.addConstraint(new MonomorphicConstraint(tlaDot, abstractRecord, tlaDot.getField(), fresh));
		return fresh;
	}

	@Override
	public Type visit(TLAExistential tlaExistential) throws RuntimeException {
		for (TLAIdentifier id : tlaExistential.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.getTypeVariable(Collections.singletonList(id)));
		}
		wrappedVisit(tlaExistential.getBody());
		return new BoolType(Collections.singletonList(tlaExistential));
	}

	@Override
	public Type visit(TLAFunction tlaFunction) throws RuntimeException {
		List<Type> keyTypes = new ArrayList<>();
		for (TLAQuantifierBound qb : tlaFunction.getArguments()) {
			keyTypes.add(processQuantifierBound(qb));
		}
		Type valueType = wrappedVisit(tlaFunction.getBody());
		Type fresh = generator.getTypeVariable(Collections.singletonList(tlaFunction));
		if (keyTypes.size() == 1) {
			solver.addConstraint(new PolymorphicConstraint(tlaFunction, Arrays.asList(
					Arrays.asList(
							new EqualityConstraint(
									mapping.get(tlaFunction.getArguments().get(0).getSet().getUID()),
									new SetType(
											generator.getTypeVariable(Collections.singletonList(tlaFunction)),
											Collections.singletonList(tlaFunction))),
							new EqualityConstraint(
									fresh,
									new MapType(
											keyTypes.get(0),
											valueType,
											Collections.singletonList(tlaFunction)))),
					Collections.singletonList(new EqualityConstraint(
							fresh,
							new FunctionType(keyTypes, valueType, Collections.singletonList(tlaFunction)))))));
			return fresh;
		}
		if (keyTypes.size() > 1) {
			List<BasicConstraint> constraintsForMap = new ArrayList<>();
			for (TLAQuantifierBound arg : tlaFunction.getArguments()) {
				constraintsForMap.add(new EqualityConstraint(
						mapping.get(arg.getSet().getUID()),
						new SetType(
								generator.getTypeVariable(Collections.singletonList(arg)),
								Collections.singletonList(tlaFunction))));
			}
			constraintsForMap.add(new EqualityConstraint(
					fresh,
					new MapType(
							new TupleType(keyTypes, Collections.singletonList(tlaFunction)),
							valueType,
							Collections.singletonList(tlaFunction))));
			solver.addConstraint(new PolymorphicConstraint(tlaFunction, Arrays.asList(
					constraintsForMap,
					Collections.singletonList(new EqualityConstraint(
							fresh,
							new FunctionType(
									keyTypes,
									valueType,
									Collections.singletonList(tlaFunction)))))));
			return fresh;
		}
		return new FunctionType(keyTypes, valueType, Collections.singletonList(tlaFunction));
	}

	@Override
	public Type visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		Type from = wrappedVisit(tlaFunctionSet.getFrom());
		Type to = wrappedVisit(tlaFunctionSet.getTo());
		solver.addConstraint(new MonomorphicConstraint(
				tlaFunctionSet,
				from,
				new SetType(
						generator.getTypeVariable(Collections.singletonList(tlaFunctionSet.getFrom())),
						Collections.singletonList(tlaFunctionSet))));
		solver.addConstraint(new MonomorphicConstraint(
				tlaFunctionSet,
				to,
				new SetType(
						generator.getTypeVariable(Collections.singletonList(tlaFunctionSet.getTo())),
						Collections.singletonList(tlaFunctionSet))));
		throw new TODO();
	}

	@Override
	public Type visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Type visit(TLAIf tlaIf) throws RuntimeException {
		solver.addConstraint(new MonomorphicConstraint(
				tlaIf, wrappedVisit(tlaIf.getCond()), new BoolType(Collections.singletonList(tlaIf.getCond()))));
		TypeVariable v = generator.getTypeVariable(Collections.singletonList(tlaIf));
		solver.addConstraint(new MonomorphicConstraint(tlaIf, wrappedVisit(tlaIf.getTval()), v));
		solver.addConstraint(new MonomorphicConstraint(tlaIf, wrappedVisit(tlaIf.getFval()), v));
		return v;
	}

	@Override
	public Type visit(TLALet tlaLet) throws RuntimeException {
		// TODO: let polymorphism
		for (TLAUnit unit : tlaLet.getDefinitions()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}
		return wrappedVisit(tlaLet.getBody());
	}

	@Override
	public Type visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaGeneralIdentifier.getUID()));
	}

	@Override
	public Type visit(TLATuple tlaTuple) throws RuntimeException {
		Type fresh = generator.getTypeVariable(Collections.singletonList(tlaTuple));
		Type elementType = generator.getTypeVariable(Collections.singletonList(tlaTuple));
		List<Type> contents = tlaTuple.getElements().stream()
				.map(this::wrappedVisit)
				.collect(Collectors.toList());
		List<BasicConstraint> commonConstraints = contents.stream()
				.map(t -> new EqualityConstraint(t, elementType))
				.collect(Collectors.toList());
		List<BasicConstraint> constraintsForChanType = new ArrayList<>(commonConstraints);
		constraintsForChanType.add(new EqualityConstraint(
				fresh,
				new ChanType(elementType, Collections.singletonList(tlaTuple))));
		List<BasicConstraint> constraintsForSliceType = new ArrayList<>(commonConstraints);
		constraintsForSliceType.add(new EqualityConstraint(
				fresh,
				new SliceType(elementType, Collections.singletonList(tlaTuple))));
		solver.addConstraint(new PolymorphicConstraint(tlaTuple, Arrays.asList(
				constraintsForSliceType,
				constraintsForChanType,
				Collections.singletonList(new EqualityConstraint(
						fresh,
						new TupleType(contents, Collections.singletonList(tlaTuple)))))));
		return fresh;
	}

	@Override
	public Type visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Type visit(TLANumber tlaNumber) throws RuntimeException {
		// TODO this check should be more sophisticated
		if (tlaNumber.getVal().contains(".")) {
			return new RealType(Collections.singletonList(tlaNumber));
		}
		return TLABuiltins.getPolymorphicNumberType(tlaNumber, solver, generator);
	}

	@Override
	public Type visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
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
	public Type visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaQuantifiedExistential.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(tlaQuantifiedExistential.getBody());
		return new BoolType(Collections.singletonList(tlaQuantifiedExistential));
	}

	@Override
	public Type visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaQuantifiedUniversal.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(tlaQuantifiedUniversal.getBody());
		return new BoolType(Collections.singletonList(tlaQuantifiedUniversal));
	}

	@Override
	public Type visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		List<RecordType.Field> fields = new ArrayList<>();
		for (TLARecordConstructor.Field field : tlaRecordConstructor.getFields()) {
			fields.add(new RecordType.Field(field.getName().getId(), wrappedVisit(field.getValue())));
		}
		return new RecordType(fields, Collections.singletonList(tlaRecordConstructor));
	}

	@Override
	public Type visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Type visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Type visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		TypeVariable elementType = generator.getTypeVariable(Collections.singletonList(tlaSetConstructor));
		for (TLAExpression element : tlaSetConstructor.getContents()) {
			solver.addConstraint(new MonomorphicConstraint(
					tlaSetConstructor, elementType, wrappedVisit(element)));
		}
		return new SetType(elementType, Collections.singletonList(tlaSetConstructor));
	}

	@Override
	public Type visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		for (TLAQuantifierBound qb : tlaSetComprehension.getBounds()) {
			processQuantifierBound(qb);
		}
		Type elementType = wrappedVisit(tlaSetComprehension.getBody());
		return new SetType(elementType, Collections.singletonList(tlaSetComprehension));
	}

	@Override
	public Type visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		Type from = wrappedVisit(tlaSetRefinement.getFrom());
		TypeVariable elementType = generator.getTypeVariable(Collections.singletonList(tlaSetRefinement));
		solver.addConstraint(new MonomorphicConstraint(
				tlaSetRefinement, from, new SetType(elementType, Collections.singletonList(tlaSetRefinement))));
		if (tlaSetRefinement.getIdent().isTuple()) {
			List<Type> elements = new ArrayList<>();
			for (TLAIdentifier id : tlaSetRefinement.getIdent().getTuple()) {
				TypeVariable v = generator.getTypeVariable(Collections.singletonList(id));
				mapping.put(id.getUID(), v);
				elements.add(v);
			}
			solver.addConstraint(new MonomorphicConstraint(
					tlaSetRefinement,
					elementType,
					new TupleType(elements, Collections.singletonList(tlaSetRefinement))));
		} else {
			TLAIdentifier id = tlaSetRefinement.getIdent().getId();
			mapping.put(id.getUID(), elementType);
		}
		Type condition = wrappedVisit(tlaSetRefinement.getWhen());
		solver.addConstraint(new MonomorphicConstraint(
				tlaSetRefinement, condition, new BoolType(Collections.singletonList(tlaSetRefinement))));
		return new SetType(elementType, Collections.singletonList(tlaSetRefinement));
	}

	@Override
	public Type visit(TLAString tlaString) throws RuntimeException {
		return new StringType(Collections.singletonList(tlaString));
	}

	@Override
	public Type visit(TLAUnary tlaUnary) throws RuntimeException {
		UID ref = registry.followReference(tlaUnary.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.constrainTypes(
				tlaUnary.getOperation(), registry,
				Collections.singletonList(wrappedVisit(tlaUnary.getOperand())),
				solver, generator, mapping);
	}

	@Override
	public Type visit(TLAUniversal tlaUniversal) throws RuntimeException {
		for (TLAIdentifier id : tlaUniversal.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.getTypeVariable(Collections.singletonList(id)));
		}
		wrappedVisit(tlaUniversal.getBody());
		return new BoolType(Collections.singletonList(tlaUniversal));
	}

	@Override
	public Type visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		TypeVariable v = generator.getTypeVariable(Collections.singletonList(plusCalDefaultInitValue));
		mapping.put(plusCalDefaultInitValue.getUID(), v);
		return v;
	}

	@Override
	public Type visit(TLAFairness fairness) throws RuntimeException{
		throw new InternalCompilerError();
	}

	@Override
	public Type visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaSpecialVariableVariable.getUID()));
	}

	@Override
	public Type visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaSpecialVariableValue.getUID()));
	}

	@Override
	public Type visit(TLARef tlaRef) throws RuntimeException {
		return typeVariableReference(registry.followReference(tlaRef.getUID()));
	}
}
