package pgo.trans.intermediate;

import java.util.*;
import java.util.stream.Collectors;

import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PGoTLAUniversal;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.type.*;
import pgo.scope.UID;

public class TLAExpressionTypeConstraintVisitor extends PGoTLAExpressionVisitor<PGoType, RuntimeException> {

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

	public PGoType wrappedVisit(PGoTLAExpression expr) {
		PGoType result = expr.accept(this);
		if (!mapping.containsKey(expr.getUID())) {
			PGoTypeVariable self = generator.get();
			solver.addConstraint(new PGoTypeMonomorphicConstraint(expr, result, self));
			mapping.put(expr.getUID(), self);
		}
		return result;
	}

	private PGoType processQuantifierBound(PGoTLAQuantifierBound qb) {
		PGoTypeVariable elementType = generator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, new PGoTypeSet(elementType, Collections.singletonList(qb)), wrappedVisit(qb.getSet())));
		switch(qb.getType()) {
		case IDS:
			for (PGoTLAIdentifier id : qb.getIds()) {
				PGoTypeVariable idType = generator.get();
				mapping.put(id.getUID(), idType);
				solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, elementType, idType));
			}
			break;
		case TUPLE:
			List<PGoType> tupleTypes = new ArrayList<>();
			for (PGoTLAIdentifier id : qb.getIds()) {
				PGoTypeVariable idType = generator.get();
				mapping.put(id.getUID(), idType);
				tupleTypes.add(idType);
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(qb, elementType, new PGoTypeTuple(tupleTypes, Collections.singletonList(qb))));
			break;
		default:
			throw new RuntimeException("unreachable");
		}
		return elementType;
	}

	@Override
	public PGoType visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		PGoType fnType = wrappedVisit(pGoTLAFunctionCall.getFunction()).substitute(solver.getMapping());
		List<PGoType> paramTypes = new ArrayList<>();
		for (PGoTLAExpression param : pGoTLAFunctionCall.getParams()) {
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
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(pGoTLAFunctionCall)))))));
		} else {
			solver.addConstraint(new PGoTypePolymorphicConstraint(pGoTLAFunctionCall, Arrays.asList(
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(
									Collections.singletonList(new PGoTypeTuple(
											paramTypes, Collections.singletonList(pGoTLAFunctionCall))),
									returnType,
									Collections.singletonList(pGoTLAFunctionCall)))),
					Collections.singletonList(new PGoTypeEqualityConstraint(
							fnType,
							new PGoTypeFunction(paramTypes, returnType, Collections.singletonList(pGoTLAFunctionCall)))))));
		}
		return returnType;
	}

	@Override
	public PGoType visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		return registry
				.findOperator(registry.followReference(pGoTLABinOp.getOperation().getUID()))
				.constrainTypes(
						pGoTLABinOp.getOperation(), registry,
						Arrays.asList(wrappedVisit(pGoTLABinOp.getLHS()), wrappedVisit(pGoTLABinOp.getRHS())),
						solver, generator, mapping);
	}

	@Override
	public PGoType visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return new PGoTypeBool(Collections.singletonList(pGoTLABool));
	}

	@Override
	public PGoType visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		for (PGoTLAIdentifier id : pGoTLAExistential.getIds()) {
			mapping.putIfAbsent(id.getUID(), generator.get());
		}
		wrappedVisit(pGoTLAExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAExistential));
	}

	@Override
	public PGoType visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		List<PGoType> keyTypes = new ArrayList<>();
		for (PGoTLAQuantifierBound qb : pGoTLAFunction.getArguments()) {
			keyTypes.add(processQuantifierBound(qb));
		}
		wrappedVisit(pGoTLAFunction.getBody());
		PGoType valueType = mapping.get(pGoTLAFunction.getBody().getUID());
		return new PGoTypeFunction(keyTypes, valueType, Collections.singletonList(pGoTLAFunction));
	}

	@Override
	public PGoType visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		PGoType from = wrappedVisit(pGoTLAFunctionSet.getFrom());
		PGoType to = wrappedVisit(pGoTLAFunctionSet.getTo());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAFunctionSet, from, new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunctionSet))));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAFunctionSet, to, new PGoTypeSet(generator.get(), Collections.singletonList(pGoTLAFunctionSet))));
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getCond()), new PGoTypeBool(Collections.singletonList(pGoTLAIf.getCond()))));
		PGoTypeVariable v = generator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getTval()), v));
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLAIf, wrappedVisit(pGoTLAIf.getFval()), v));
		return v;
	}

	@Override
	public PGoType visit(PGoTLALet pGoTLALet) throws RuntimeException {
		// TODO: let polymorphism
		for (PGoTLAUnit unit : pGoTLALet.getDefinitions()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(registry, solver, generator, mapping));
		}
		return wrappedVisit(pGoTLALet.getBody());
	}

	@Override
	public PGoType visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
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
	public PGoType visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		Map<Integer, PGoType> elementTypes = new HashMap<>();
		List<PGoTLAExpression> elements = pGoTLATuple.getElements();
		for (int i = 0; i < elements.size(); ++i) {
			elementTypes.put(i, wrappedVisit(elements.get(i)));
		}
		return new PGoTypeUnrealizedTuple(elementTypes, Collections.singletonList(pGoTLATuple));
	}

	@Override
	public PGoType visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		// TODO this check should be more sophisticated
		if (pGoTLANumber.getVal().contains(".")) {
			return new PGoTypeDecimal(Collections.singletonList(pGoTLANumber));
		}
		return new PGoTypeUnrealizedNumber(new PGoTypeInt(Collections.singletonList(pGoTLANumber)), Collections.singletonList(pGoTLANumber));
	}

	@Override
	public PGoType visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
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
	public PGoType visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		for (PGoTLAQuantifierBound qb : pGoTLAQuantifiedExistential.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(pGoTLAQuantifiedExistential.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAQuantifiedExistential));
	}

	@Override
	public PGoType visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		for (PGoTLAQuantifierBound qb : pGoTLAQuantifiedUniversal.getIds()) {
			processQuantifierBound(qb);
		}
		wrappedVisit(pGoTLAQuantifiedUniversal.getBody());
		return new PGoTypeBool(Collections.singletonList(pGoTLAQuantifiedUniversal));
	}

	@Override
	public PGoType visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public PGoType visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		PGoTypeVariable elementType = generator.get();
		for (PGoTLAExpression element : pGoTLASetConstructor.getContents()) {
			solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetConstructor, elementType, wrappedVisit(element)));
		}
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetConstructor));
	}

	@Override
	public PGoType visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		for (PGoTLAQuantifierBound qb : pGoTLASetComprehension.getBounds()) {
			processQuantifierBound(qb);
		}
		PGoType elementType = wrappedVisit(pGoTLASetComprehension.getBody());
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetComprehension));
	}

	@Override
	public PGoType visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		PGoType from = wrappedVisit(pGoTLASetRefinement.getFrom());
		PGoTypeVariable elementType = generator.get();
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, from, new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetRefinement))));
		if (pGoTLASetRefinement.getIdent().isTuple()) {
			List<PGoType> elements = new ArrayList<>();
			for (PGoTLAIdentifier id : pGoTLASetRefinement.getIdent().getTuple()) {
				PGoTypeVariable v = generator.get();
				mapping.put(id.getUID(), v);
				elements.add(v);
			}
			solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, elementType, new PGoTypeTuple(elements, Collections.singletonList(pGoTLASetRefinement))));
		} else {
			PGoTLAIdentifier id = pGoTLASetRefinement.getIdent().getId();
			mapping.put(id.getUID(), elementType);
		}
		PGoType condition = wrappedVisit(pGoTLASetRefinement.getWhen());
		solver.addConstraint(new PGoTypeMonomorphicConstraint(pGoTLASetRefinement, condition, new PGoTypeBool(Collections.singletonList(pGoTLASetRefinement))));
		return new PGoTypeSet(elementType, Collections.singletonList(pGoTLASetRefinement));
	}

	@Override
	public PGoType visit(PGoTLAString pGoTLAString) throws RuntimeException {
		return new PGoTypeString(Collections.singletonList(pGoTLAString));
	}

	@Override
	public PGoType visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		UID ref = registry.followReference(pGoTLAUnary.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.constrainTypes(
				pGoTLAUnary.getOperation(), registry,
				Collections.singletonList(wrappedVisit(pGoTLAUnary.getOperand())),
				solver, generator, mapping);
	}

	@Override
	public PGoType visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		for (PGoTLAIdentifier id : pGoTLAUniversal.getIds()) {
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

}
