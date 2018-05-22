package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
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
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeBool;
import pgo.model.type.PGoTypeConstraint;
import pgo.model.type.PGoTypeGenerator;
import pgo.model.type.PGoTypeNatural;
import pgo.model.type.PGoTypeSet;
import pgo.model.type.PGoTypeSolver;
import pgo.model.type.PGoTypeTuple;
import pgo.model.type.PGoTypeVariable;
import pgo.scope.UID;

public class TLAExpressionTypeConstraintVisitor extends PGoTLAExpressionVisitor<PGoType, RuntimeException> {
	
	private PGoTypeSolver solver;
	private PGoTypeGenerator generator;
	private Map<UID, PGoTypeVariable> mapping;

	public TLAExpressionTypeConstraintVisitor(PGoTypeSolver solver, PGoTypeGenerator generator, Map<UID, PGoTypeVariable> mapping) {
		this.solver = solver;
		this.generator = generator;
		this.mapping = mapping;
	}

	@Override
	public PGoType visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		// TODO
		return null;
	}

	@Override
	public PGoType visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return PGoTypeBool.getInstance();
	}

	@Override
	public PGoType visit(PGoTLACase pGoTLACase) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		PGoType from = pGoTLAFunctionSet.getFrom().accept(this);
		PGoType to = pGoTLAFunctionSet.getTo().accept(this);
		solver.accept(new PGoTypeConstraint(from, new PGoTypeSet(generator.get())));
		solver.accept(new PGoTypeConstraint(to, new PGoTypeSet(generator.get())));
		return null;
	}

	@Override
	public PGoType visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		solver.accept(new PGoTypeConstraint(pGoTLAIf.getCond().accept(this), PGoTypeBool.getInstance()));
		PGoTypeVariable v = generator.get();
		solver.accept(new PGoTypeConstraint(pGoTLAIf.getTval().accept(this), v));
		solver.accept(new PGoTypeConstraint(pGoTLAIf.getFval().accept(this), v));
		return v;
	}

	@Override
	public PGoType visit(PGoTLALet pGoTLALet) throws RuntimeException {
		// TODO: let polymorphism
		for(PGoTLAUnit unit : pGoTLALet.getDefinitions()) {
			unit.accept(new TLAUnitTypeConstraintVisitor(solver, generator, mapping));
		}
		return pGoTLALet.getBody().accept(this);
	}

	@Override
	public PGoType visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		if(mapping.containsKey(pGoTLAVariable.getUID())){
			return mapping.get(pGoTLAVariable.getUID());
		}else {
			PGoTypeVariable v = generator.get();
			mapping.put(pGoTLAVariable.getUID(), v);
			return v;
		}
	}

	@Override
	public PGoType visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		List<PGoType> elementTypes = new ArrayList<>();
		for(PGoTLAExpression element : pGoTLATuple.getElements()) {
			elementTypes.add(element.accept(this));
		}
		return new PGoTypeTuple(elementTypes);
	}

	@Override
	public PGoType visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		return PGoTypeNatural.getInstance();
	}

	@Override
	public PGoType visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAString pGoTLAString) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PGoType visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// this expression should never have any effect on variable type
		return generator.get();
	}

}
