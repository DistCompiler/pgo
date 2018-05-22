package pgo.trans.intermediate;

import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLACaseArm;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAFunctionSubstitutionPair;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAIdentifierOrTuple;
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

public class TLAExpressionScopingVisitor extends PGoTLAExpressionVisitor<Void, RuntimeException> {

	TLAScopeBuilder builder;

	public TLAExpressionScopingVisitor(TLAScopeBuilder builder) {
		this.builder = builder;
	}

	@Override
	public Void visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		pGoTLAFunctionCall.getFunction().accept(this);
		for(PGoTLAExpression param : pGoTLAFunctionCall.getParams()) {
			param.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(pGoTLABinOp.getPrefix(), pGoTLABinOp.getOperation().getValue()),
				pGoTLABinOp.getOperation().getUID());
		pGoTLABinOp.getLHS().accept(this);
		pGoTLABinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLABool pGoTLABool) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(PGoTLACase pGoTLACase) throws RuntimeException {
		for(PGoTLACaseArm arm : pGoTLACase.getArms()) {
			arm.getCondition().accept(this);
			arm.getResult().accept(this);
		}
		if(pGoTLACase.getOther() != null) {
			pGoTLACase.getOther().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAIdentifier id : pGoTLAExistential.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		pGoTLAExistential.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		TLAScopeBuilder argScope = builder.makeNestedScope();
		for(PGoTLAQuantifierBound qb : pGoTLAFunction.getArguments()) {
			for(PGoTLAIdentifier id : qb.getIds()) {
				argScope.defineLocal(id.getId(), id.getUID());
			}
			qb.getSet().accept(this);
		}
		pGoTLAFunction.getBody().accept(new TLAExpressionScopingVisitor(argScope));
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		pGoTLAFunctionSet.getFrom().accept(this);
		pGoTLAFunctionSet.getTo().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		pGoTLAFunctionSubstitution.getSource().accept(this);
		for(PGoTLAFunctionSubstitutionPair pair : pGoTLAFunctionSubstitution.getSubstitutions()) {
			pair.getValue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		pGoTLAIf.getCond().accept(this);
		pGoTLAIf.getTval().accept(this);
		pGoTLAIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLALet pGoTLALet) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAUnit unit : pGoTLALet.getDefinitions()) {
			// TODO: fix this part
			//unit.accept(new PGoTLAUnitScopingVisitor(nested));
		}
		pGoTLALet.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		builder.reference(QualifiedName.fromTLAPrefix(pGoTLAVariable.getGeneralIdentifierPrefix(), pGoTLAVariable.getName().getId()), pGoTLAVariable.getUID());
		return null;
	}

	@Override
	public Void visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		for(PGoTLAExpression element : pGoTLATuple.getElements()) {
			element.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		pGoTLAMaybeAction.getBody().accept(this);
		pGoTLAMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(pGoTLAOperatorCall.getPrefix(), pGoTLAOperatorCall.getName().getId()),
				pGoTLAOperatorCall.getName().getUID());
		for(PGoTLAExpression arg : pGoTLAOperatorCall.getArgs()) {
			arg.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAQuantifierBound qb : pGoTLAQuantifiedExistential.getIds()) {
			for(PGoTLAIdentifier id : qb.getIds()) {
				nested.defineLocal(id.getId(), id.getUID());
			}
			qb.getSet().accept(this);
		}
		pGoTLAQuantifiedExistential.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAQuantifierBound qb : pGoTLAQuantifiedUniversal.getIds()) {
			for(PGoTLAIdentifier id : qb.getIds()) {
				nested.defineLocal(id.getId(), id.getUID());
			}
			qb.getSet().accept(this);
		}
		pGoTLAQuantifiedUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		for(PGoTLARecordConstructor.Field f : pGoTLARecordConstructor.getFields()) {
			f.getValue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		for(PGoTLARecordSet.Field f : pGoTLARecordSet.getFields()) {
			f.getSet().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		pGoTLARequiredAction.getBody().accept(this);
		pGoTLARequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		for(PGoTLAExpression elem : pGoTLASetConstructor.getContents()) {
			elem.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAQuantifierBound qb : pGoTLASetComprehension.getBounds()) {
			for(PGoTLAIdentifier id : qb.getIds()) {
				nested.defineLocal(id.getId(), id.getUID());
			}
			qb.getSet().accept(this);
		}
		pGoTLASetComprehension.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		TLAScopeBuilder nested = builder.makeNestedScope();
		PGoTLAIdentifierOrTuple ident = pGoTLASetRefinement.getIdent();
		if(ident.isTuple()) {
			for(PGoTLAIdentifier id : ident.getTuple()) {
				nested.defineLocal(id.getId(), id.getUID());
			}
		}else {
			nested.defineLocal(ident.getId().getId(), ident.getId().getUID());
		}
		pGoTLASetRefinement.getWhen().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PGoTLAString pGoTLAString) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		builder.reference(QualifiedName.fromTLAPrefix(pGoTLAUnary.getPrefix(), pGoTLAUnary.getOperation()), pGoTLAUnary.getUID());
		pGoTLAUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for(PGoTLAIdentifier id : pGoTLAUniversal.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		pGoTLAUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested));
		return null;
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// has no effect on scoping
		return null;
	}

}
