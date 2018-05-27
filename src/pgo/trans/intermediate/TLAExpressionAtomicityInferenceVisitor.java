package pgo.trans.intermediate;

import pgo.model.tla.*;
import pgo.scope.UID;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Consumer;

public class TLAExpressionAtomicityInferenceVisitor extends PGoTLAExpressionVisitor<Set<UID>, RuntimeException> {
	protected Consumer<UID> captureRead;

	public TLAExpressionAtomicityInferenceVisitor(Consumer<UID> captureRead) {
		this.captureRead = captureRead;
	}

	@Override
	public Set<UID> visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		pGoTLAFunctionCall.getFunction().accept(this);
		pGoTLAFunctionCall.getParams().forEach(e -> e.accept(this));
		return Collections.singleton(pGoTLAFunctionCall.getFunction().getUID());
	}

	@Override
	public Set<UID> visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		pGoTLABinOp.getLHS().accept(this);
		pGoTLABinOp.getRHS().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Set<UID> visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		return pGoTLAExistential.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		pGoTLAFunction.getArguments().forEach(a -> a.getSet().accept(this));
		return pGoTLAFunction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		pGoTLAFunctionSet.getFrom().accept(this);
		pGoTLAFunctionSet.getTo().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Set<UID> visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		pGoTLAIf.getCond().accept(this);
		Set<UID> ret = new HashSet<>(pGoTLAIf.getTval().accept(this));
		ret.addAll(pGoTLAIf.getFval().accept(this));
		return ret;
	}

	@Override
	public Set<UID> visit(PGoTLALet pGoTLALet) throws RuntimeException {
		pGoTLALet.getDefinitions().forEach(def -> def.accept(new TLAUnitAtomicityInferenceVisitor(this)));
		return pGoTLALet.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		captureRead.accept(pGoTLAVariable.getUID());
		return Collections.singleton(pGoTLAVariable.getUID());
	}

	@Override
	public Set<UID> visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		pGoTLATuple.getElements().forEach(e -> e.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		return pGoTLAMaybeAction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		pGoTLAOperatorCall.getArgs().forEach(a -> a.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		return pGoTLAQuantifiedExistential.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return pGoTLAQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		pGoTLARecordConstructor.getFields().forEach(f -> f.getValue().accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		pGoTLARecordSet.getFields().forEach(f -> f.getSet().accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		return pGoTLARequiredAction.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		pGoTLASetConstructor.getContents().forEach(e -> e.accept(this));
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		pGoTLASetComprehension.getBounds().forEach(b -> b.getSet().accept(this));
		pGoTLASetComprehension.getBody().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		pGoTLASetRefinement.getWhen().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAString pGoTLAString) throws RuntimeException {
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		pGoTLAUnary.getOperand().accept(this);
		return Collections.emptySet();
	}

	@Override
	public Set<UID> visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		return pGoTLAUniversal.getBody().accept(this);
	}

	@Override
	public Set<UID> visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return Collections.emptySet();
	}
}
