package pgo.trans.passes.atomicity;

import pgo.TODO;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.TLAUnitAtomicityInferenceVisitor;

import java.util.function.Consumer;

public class TLAExpressionValueAtomicityInferenceVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	protected Consumer<UID> captureRead;

	public TLAExpressionValueAtomicityInferenceVisitor(Consumer<UID> captureRead) {
		this.captureRead = captureRead;
	}

	@Override
	public Void visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		pGoTLAFunctionCall.getFunction().accept(this);
		pGoTLAFunctionCall.getParams().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLABinOp TLABinOp) throws RuntimeException {
		TLABinOp.getLHS().accept(this);
		TLABinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(TLABool TLABool) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLACase TLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLAExistential TLAExistential) throws RuntimeException {
		TLAExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		pGoTLAFunction.getArguments().forEach(a -> a.getSet().accept(this));
		pGoTLAFunction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		pGoTLAFunctionSet.getFrom().accept(this);
		pGoTLAFunctionSet.getTo().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLAIf pGoTLAIf) throws RuntimeException {
		pGoTLAIf.getCond().accept(this);
		pGoTLAIf.getTval().accept(this);
		pGoTLAIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(TLALet pGoTLALet) throws RuntimeException {
		pGoTLALet.getDefinitions().forEach(def -> def.accept(new TLAUnitAtomicityInferenceVisitor(this)));
		pGoTLALet.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		captureRead.accept(pGoTLAVariable.getUID());
		return null;
	}

	@Override
	public Void visit(TLATuple pGoTLATuple) throws RuntimeException {
		pGoTLATuple.getElements().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		pGoTLAMaybeAction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber pGoTLANumber) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		pGoTLAOperatorCall.getArgs().forEach(a -> a.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		pGoTLAQuantifiedExistential.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return pGoTLAQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Void visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		pGoTLARecordConstructor.getFields().forEach(f -> f.getValue().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		pGoTLARecordSet.getFields().forEach(f -> f.getSet().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		return pGoTLARequiredAction.getBody().accept(this);
	}

	@Override
	public Void visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		pGoTLASetConstructor.getContents().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		pGoTLASetComprehension.getBounds().forEach(b -> b.getSet().accept(this));
		pGoTLASetComprehension.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		pGoTLASetRefinement.getWhen().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAString pGoTLAString) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		pGoTLAUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		pGoTLAUniversal.getBody().accept(this);
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
