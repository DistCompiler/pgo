package pgo.trans.passes.type;

import java.util.*;
import java.util.stream.Collectors;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.model.type.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.OperatorAccessor;

public class TLAExpressionTypeConstraintVisitor extends TLAExpressionVisitor<PGoType, RuntimeException> {

	private PGoTypeSolver solver;
	private PGoTypeGenerator generator;
	private Map<UID, PGoTypeVariable> mapping;
	private DefinitionRegistry registry;

	public TLAExpressionTypeConstraintVisitor(DefinitionRegistry registry, PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.registry = registry;
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	public PGoType wrappedVisit(TLAExpression expr) {
		PGoType result = expr.accept(this);
		if (!mapping.containsKey(expr.getUID())) {
			PGoTypeVariable self = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(expr, result, self));
			mapping.put(expr.getUID(), self);
		}
		return result;
	}

	private PGoType processQuantifierBound(TLAQuantifierBound qb) {
		PGoTypeVariable elementType = generator.get();
		solver.addConstraint(new PGoTypePolymorphicConstraint(qb, Arrays.asList(
				Collections.singletonList(new PGoTypeEqualityConstraint(
						new PGoTypeSet(elementType, Collections.singletonList(qb)),
						wrappedVisit(qb.getSet()))),
				Collections.singletonList(new PGoTypeEqualityConstraint(
						new PGoTypeNonEnumerableSet(elementType, Collections.singletonList(qb)),
						wrappedVisit(qb.getSet()))))));
		switch(qb.getType()) {
		case IDS:
			for (TLAIdentifier id : qb.getIds()) {
				PGoTypeVariable idType = generator.get();
				mapping.put(id.getUID(), idType);
				solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, elementType, idType));
			}
			break;
		case TUPLE:
			List<PGoType> tupleTypes = new ArrayList<>();
			for (TLAIdentifier id : qb.getIds()) {
				PGoTypeVariable idType = generator.get();
				mapping.put(id.getUID(), idType);
				tupleTypes.add(idType);
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, elementType, new PGoTypeTuple(tupleTypes, Collections.singletonList(qb))));
			break;
		default:
			throw new Unreachable();
		}
		return elementType;
	}

	@Override
	public PGoType visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		PGoType fnType = wrappedVisit(pGoTLAFunctionCall.getFunction()).substitute(solver.getMapping());
		List<PGoType> paramTypes = new ArrayList<>();
		for (TLAExpression param : pGoTLAFunctionCall.getParams()) {
			paramTypes.add(wrappedVisit(param));
		}
		PGoTypeVariable returnType = generator.get();
		if (paramTypes.size() == 1) {
			solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLAFunctionCall, Arrays.asList(
					Arrays.asList(
							new PGoTypeEqualityConstraint(
									fnType,
									new PGoTypeSlice(returnType, Collections.singletonList(pGoTLAFunctionCall))),
							new PGoTypeEqualityConstraint(
									paramTypes.get(0),
									new PGoTypeInt(Collections.singletonList(pGoTLAFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeMap(paramTypes.get(0), returnType, Collections.singletonList(pGoTLAFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(pGoTLAFunctionCall)))))));
		} else {
			solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLAFunctionCall, Arrays.asList(
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeMap(
									new PGoTypeTuple(paramTypes, Collections.singletonList(pGoTLAFunctionCall)),
									returnType,
									Collections.singletonList(pGoTLAFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(pGoTLAFunctionCall)))))));
		}
		return returnType;
	}

	@Override
	public PGoType visit(TLABinOp TLABinOp) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(TLABinOp.getOperation().getUID()))
				.constrainTypes(
						TLABinOp.getOperation(), registry,
						Arrays.asList(wrappedVisit(TLABinOp.getLHS()), wrappedVisit(TLABinOp.getRHS())),
						solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLABool TLABool) throws RuntimeException {
		return new PGoTypeBool(Collections.singletonList(TLABool));
	}

	@Override
	public PGoType visit(TLACase tlaCase) throws RuntimeException {
		PGoTypeVariable v = generator.get();
		for (TLACaseArm caseArm : tlaCase.getArms()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaCase, wrappedVisit(caseArm.getCondition()), new PGoTypeBool(Collections.singletonList(caseArm.getCondition()))));
			solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaCase, wrappedVisit(caseArm.getResult()), v));
		}

		if (tlaCase.getOther() != null) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(tlaCase, wrappedVisit(tlaCase.getOther()), v));
		}

		return v;
	}

	@Override
	public PGoType visit(TLAExistential TLAExistential) throws RuntimeException {
		for (TLAIdentifier id : TLAExistential.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.get());
		}
		wrappedVisit(TLAExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(TLAExistential));
	}

	@Override
	public PGoType visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		List<PGoType> keyTypes = new ArrayList<>();
		for (TLAQuantifierBound qb : pGoTLAFunction.getArguments()) {
			keyTypes.add(processQuantifierBound(qb));
		}
		PGoType valueType = wrappedVisit(pGoTLAFunction.getBody());
		PGoType fresh = generator.get();
		if (keyTypes.size() == 1) {
			solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLAFunction, Arrays.asList(
					Arrays.asList(
							new PGoTypeEqualityConstraint(
									mapping.get(pGoTLAFunction.getArguments().get(0).getSet().getUID()),
									new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunction))),
							new PGoTypeEqualityConstraint(
									fresh,
									new PGoTypeMap(
											keyTypes.get(0),
											valueType,
											Collections.singletonList(pGoTLAFunction)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fresh,
							new PGoTypeFunction(keyTypes, valueType, Collections.singletonList(pGoTLAFunction)))))));
			return fresh;
		}
		if (keyTypes.size() > 1) {
			List<PGoTypeEqualityConstraint> constraintsForMap = new ArrayList<>();
			for (TLAQuantifierBound arg : pGoTLAFunction.getArguments()) {
				constraintsForMap.add(new PGoTypeEqualityConstraint(
						mapping.get(arg.getSet().getUID()),
						new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunction))));
			}
			constraintsForMap.add(new PGoTypeEqualityConstraint(
					fresh,
					new PGoTypeMap(
							new PGoTypeTuple(keyTypes, Collections.singletonList(pGoTLAFunction)),
							valueType,
							Collections.singletonList(pGoTLAFunction))));
			solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLAFunction, Arrays.asList(
					constraintsForMap,
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fresh,
							new PGoTypeFunction(
									keyTypes,
									valueType,
									Collections.singletonList(pGoTLAFunction)))))));
			return fresh;
		}
		return new PGoTypeFunction(keyTypes, valueType, Collections.singletonList(pGoTLAFunction));
	}

	@Override
	public PGoType visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		PGoType from = wrappedVisit(pGoTLAFunctionSet.getFrom());
		PGoType to = wrappedVisit(pGoTLAFunctionSet.getTo());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAFunctionSet, from, new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunctionSet))));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAFunctionSet, to, new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunctionSet))));
		throw new TODO();
	}

	@Override
	public PGoType visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLAIf pGoTLAIf) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getCond()), new PGoTypeBool(Collections.singletonList(pGoTLAIf.getCond()))));
		PGoTypeVariable v = generator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getTval()), v));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getFval()), v));
		return v;
	}

	@Override
	public PGoType visit(TLALet pGoTLALet) throws RuntimeException {
		// TODO: let polymorphism
		for (TLAUnit unit : pGoTLALet.getDefinitions()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}
		return wrappedVisit(pGoTLALet.getBody());
	}

	@Override
	public PGoType visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		UID uid = registry.followReference(pGoTLAVariable.getUID());
		if (mapping.containsKey(uid)){
			return mapping.get(uid);
		} else {
			PGoTypeVariable v = generator.get();
			mapping.put(uid, v);
			return v;
		}
	}

	@Override
	public PGoType visit(TLATuple pGoTLATuple) throws RuntimeException {
		PGoType fresh = generator.get();
		PGoType elementType = generator.get();
		List<PGoType> contents = pGoTLATuple.getElements().stream()
				.map(this::wrappedVisit)
				.collect(Collectors.toList());
		List<PGoTypeEqualityConstraint> commonConstraints = contents.stream()
				.map(t -> new PGoTypeEqualityConstraint(t, elementType))
				.collect(Collectors.toList());
		List<PGoTypeEqualityConstraint> constraintsForChanType = new ArrayList<>(commonConstraints);
		constraintsForChanType.add(new PGoTypeEqualityConstraint(
				fresh,
				new PGoTypeChan(elementType, Collections.singletonList(pGoTLATuple))));
		List<PGoTypeEqualityConstraint> constraintsForSliceType = new ArrayList<>(commonConstraints);
		constraintsForSliceType.add(new PGoTypeEqualityConstraint(
				fresh,
				new PGoTypeSlice(elementType, Collections.singletonList(pGoTLATuple))));
		solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLATuple, Arrays.asList(
				constraintsForChanType,
				constraintsForSliceType,
				Collections.singletonList(new PGoTypeEqualityConstraint(
						fresh,
						new PGoTypeTuple(contents, Collections.singletonList(pGoTLATuple)))))));
		return fresh;
	}

	@Override
	public PGoType visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLANumber pGoTLANumber) throws RuntimeException {
		// TODO this check should be more sophisticated
		if (pGoTLANumber.getVal().contains(".")) {
			return new PGoTypeDecimal(Collections.singletonList(pGoTLANumber));
		}
		return new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(pGoTLANumber)), Collections.singletonList(pGoTLANumber));
	}

	@Override
	public PGoType visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLAOperatorCall.getName().getUID()))
				.constrainTypes(
						pGoTLAOperatorCall, registry,
						pGoTLAOperatorCall.getArgs().stream()
								.map(this::wrappedVisit)
								.collect(Collectors.toList()),
						solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		for (TLAQuantifierBound qb : pGoTLAQuantifiedExistential.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(pGoTLAQuantifiedExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAQuantifiedExistential));
	}

	@Override
	public PGoType visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		for (TLAQuantifierBound qb : pGoTLAQuantifiedUniversal.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(pGoTLAQuantifiedUniversal.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAQuantifiedUniversal));
	}

	@Override
	public PGoType visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public PGoType visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		PGoTypeVariable elementType = generator.get();
		for (TLAExpression element : pGoTLASetConstructor.getContents()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetConstructor, elementType, wrappedVisit(element)));
		}
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetConstructor));
	}

	@Override
	public PGoType visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		for (TLAQuantifierBound qb : pGoTLASetComprehension.getBounds()) {
			processQuantifierBound(qb);
		}
		PGoType elementType = wrappedVisit(pGoTLASetComprehension.getBody());
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetComprehension));
	}

	@Override
	public PGoType visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		PGoType from = wrappedVisit(pGoTLASetRefinement.getFrom());
		PGoTypeVariable elementType = generator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, from, new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetRefinement))));
		if (pGoTLASetRefinement.getIdent().isTuple()) {
			List<PGoType> elements = new ArrayList<>();
			for (TLAIdentifier id : pGoTLASetRefinement.getIdent().getTuple()) {
				PGoTypeVariable v = generator.get();
				mapping.put(id.getUID(), v);
				elements.add(v);
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, elementType, new PGoTypeTuple(elements, Collections.singletonList(pGoTLASetRefinement))));
		} else {
			TLAIdentifier id = pGoTLASetRefinement.getIdent().getId();
			mapping.put(id.getUID(), elementType);
		}
		PGoType condition = wrappedVisit(pGoTLASetRefinement.getWhen());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, condition, new PGoTypeBool(Collections.singletonList(pGoTLASetRefinement))));
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetRefinement));
	}

	@Override
	public PGoType visit(TLAString pGoTLAString) throws RuntimeException {
		return new PGoTypeString(Collections.singletonList(pGoTLAString));
	}

	@Override
	public PGoType visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		UID ref = registry.followReference(pGoTLAUnary.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.constrainTypes(
				pGoTLAUnary.getOperation(), registry,
				Collections.singletonList(wrappedVisit(pGoTLAUnary.getOperand())),
				solver, generator, mapping);
	}

	@Override
	public PGoType visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		for (TLAIdentifier id : pGoTLAUniversal.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.get());
		}
		wrappedVisit(pGoTLAUniversal.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAUniversal));
	}

	@Override
	public PGoType visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		PGoTypeVariable v = generator.get();
		mapping.put(plusCalDefaultInitValue.getUID(), v);
		return v;
	}

	@Override
	public PGoType visit(TLAFairness fairness) throws RuntimeException{
		throw new InternalCompilerError();
	}

}
