package pgo.trans.passes.atomicity;

import pgo.TODO;
import pgo.model.tla.*;
import pgo.scope.UID;

import java.util.function.Consumer;

public class TLAExpressionValueAtomicityInferenceVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	protected Consumer<TLAExpression> captureRead;

	public TLAExpressionValueAtomicityInferenceVisitor(Consumer<TLAExpression> captureRead) {
		this.captureRead = captureRead;
	}

	@Override
	public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		captureRead.accept(tlaFunctionCall);

		tlaFunctionCall.getFunction().accept(this);
		tlaFunctionCall.getParams().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLABinOp tlaBinOp) throws RuntimeException {
		tlaBinOp.getLHS().accept(this);
		tlaBinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(TLABool tlaBool) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLACase tlaCase) throws RuntimeException {
		for (TLACaseArm arm : tlaCase.getArms()) {
			arm.getCondition().accept(this);
			arm.getResult().accept(this);
		}
		tlaCase.getOther().accept(this);
		return null;
	}

	@Override
	public Void visit(TLADot tlaDot) throws RuntimeException {
		tlaDot.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws RuntimeException {
		tlaExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws RuntimeException {
		tlaFunction.getArguments().forEach(a -> a.getSet().accept(this));
		tlaFunction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		tlaFunctionSet.getFrom().accept(this);
		tlaFunctionSet.getTo().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLAIf tlaIf) throws RuntimeException {
		tlaIf.getCond().accept(this);
		tlaIf.getTval().accept(this);
		tlaIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(TLALet tlaLet) throws RuntimeException {
		tlaLet.getDefinitions().forEach(def -> def.accept(new TLAUnitAtomicityInferenceVisitor(this)));
		tlaLet.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		captureRead.accept(tlaGeneralIdentifier);
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws RuntimeException {
		tlaTuple.getElements().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		tlaMaybeAction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		tlaOperatorCall.getArgs().forEach(a -> a.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		tlaQuantifiedExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return tlaQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		tlaRecordConstructor.getFields().forEach(f -> f.getValue().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		tlaRecordSet.getFields().forEach(f -> f.getSet().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return tlaRequiredAction.getBody().accept(this);
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		tlaSetConstructor.getContents().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		tlaSetComprehension.getBounds().forEach(b -> b.getSet().accept(this));
		tlaSetComprehension.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		tlaSetRefinement.getFrom().accept(this);
		tlaSetRefinement.getWhen().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAString tlaString) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws RuntimeException {
		tlaUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
		tlaUniversal.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAFairness fairness) throws RuntimeException{
		throw new TODO();
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		throw new TODO();
	}
}
