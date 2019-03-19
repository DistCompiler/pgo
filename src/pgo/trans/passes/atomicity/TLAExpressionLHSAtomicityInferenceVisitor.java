package pgo.trans.passes.atomicity;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.scope.UID;

import java.util.function.Consumer;

public class TLAExpressionLHSAtomicityInferenceVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	private TLAExpressionValueAtomicityInferenceVisitor visitor;
	private Consumer<TLAExpression> captureWrite;

	public TLAExpressionLHSAtomicityInferenceVisitor(TLAExpressionValueAtomicityInferenceVisitor visitor,
	                                                 Consumer<TLAExpression> captureWrite) {
		this.visitor = visitor;
		this.captureWrite = captureWrite;
	}

	@Override
	public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		captureWrite.accept(tlaFunctionCall);
		tlaFunctionCall.getFunction().accept(this);
		tlaFunctionCall.getParams().forEach(p -> p.accept(visitor));
		return null;
	}

	@Override
	public Void visit(TLABinOp tlaBinOp) throws RuntimeException {
        throw new Unreachable();
	}

	@Override
	public Void visit(TLABool tlaBool) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLACase tlaCase) throws RuntimeException {
        throw new TODO();
	}

	@Override
	public Void visit(TLADot tlaDot) throws RuntimeException {
		tlaDot.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAIf tlaIf) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLALet tlaLet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		captureWrite.accept(tlaGeneralIdentifier);
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAString tlaString) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
