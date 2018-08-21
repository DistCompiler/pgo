package pgo.trans.intermediate;

import pgo.TODO;
import pgo.model.tla.*;
import pgo.scope.UID;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Consumer;

public class TLAExpressionAtomicityInferenceVisitor extends TLAExpressionVisitor<Set<UID>, RuntimeException> {
	protected Consumer<UID> captureRead;

	public TLAExpressionAtomicityInferenceVisitor(Consumer<UID> captureRead) {
		this.captureRead = captureRead;
	}

	@Override
	public Set<UID> visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		pGoTLAFunctionCall.getFunction().accept(this);
		pGoTLAFunctionCall.getParams().forEach(e -> e.accept(this));
		return Collections.singleton(pGoTLAFunctionCall.getFunction().getUID());
	}

	@Override
	public Set<UID> visit(TLABinOp TLABinOp) throws RuntimeException {
		TLABinOp.getLHS().accept(this);
		TLABinOp.getRHS().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLABool TLABool) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLACase TLACase) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Set<UID> visit(TLAExistential TLAExistential) throws RuntimeException {
		return TLAExistential.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		pGoTLAFunction.getArguments().forEach(a -> a.getSet().accept(this));
		return pGoTLAFunction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		pGoTLAFunctionSet.getFrom().accept(this);
		pGoTLAFunctionSet.getTo().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Set<UID> visit(TLAIf pGoTLAIf) throws RuntimeException {
		pGoTLAIf.getCond().accept(this);
		Set<UID> ret = new HashSet<>(pGoTLAIf.getTval().accept(this));
		ret.addAll(pGoTLAIf.getFval().accept(this));
		return ret;
	}

	@Override
	public Set<UID> visit(TLALet pGoTLALet) throws RuntimeException {
		pGoTLALet.getDefinitions().forEach(def -> def.accept(new TLAUnitAtomicityInferenceVisitor(this)));
		return pGoTLALet.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		captureRead.accept(pGoTLAVariable.getUID());
		return Collections.singleton(pGoTLAVariable.getUID());
	}

	@Override
	public Set<UID> visit(TLATuple pGoTLATuple) throws RuntimeException {
		pGoTLATuple.getElements().forEach(e -> e.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		return pGoTLAMaybeAction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLANumber pGoTLANumber) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		pGoTLAOperatorCall.getArgs().forEach(a -> a.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		return pGoTLAQuantifiedExistential.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return pGoTLAQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		pGoTLARecordConstructor.getFields().forEach(f -> f.getValue().accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		pGoTLARecordSet.getFields().forEach(f -> f.getSet().accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		return pGoTLARequiredAction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		pGoTLASetConstructor.getContents().forEach(e -> e.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		pGoTLASetComprehension.getBounds().forEach(b -> b.getSet().accept(this));
		pGoTLASetComprehension.getBody().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		pGoTLASetRefinement.getWhen().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAString pGoTLAString) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		pGoTLAUnary.getOperand().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		return pGoTLAUniversal.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(TLAFairness fairness) throws RuntimeException{
		throw new TODO();
	}
}
