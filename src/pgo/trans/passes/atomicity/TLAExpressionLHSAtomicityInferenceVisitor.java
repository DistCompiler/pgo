package pgo.trans.passes.atomicity;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.scope.UID;

import java.util.function.Consumer;

public class TLAExpressionLHSAtomicityInferenceVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	private TLAExpressionValueAtomicityInferenceVisitor visitor;
	private Consumer<UID> captureWrite;

	public TLAExpressionLHSAtomicityInferenceVisitor(TLAExpressionValueAtomicityInferenceVisitor visitor,
	                                                 Consumer<UID> captureWrite) {
		this.visitor = visitor;
		this.captureWrite = captureWrite;
	}

	@Override
	public Void visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		for (TLAExpression param : pGoTLAFunctionCall.getParams()) {
			param.accept(visitor);
		}
		captureWrite.accept(pGoTLAFunctionCall.getFunction().getUID());
		return null;
	}

	@Override
	public Void visit(TLABinOp TLABinOp) throws RuntimeException {
        throw new Unreachable();
	}

	@Override
	public Void visit(TLABool TLABool) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLACase TLACase) throws RuntimeException {
        throw new TODO();
	}

	@Override
	public Void visit(TLAExistential TLAExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAIf pGoTLAIf) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLALet pGoTLALet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		captureWrite.accept(pGoTLAVariable.getUID());
		return null;
	}

	@Override
	public Void visit(TLATuple pGoTLATuple) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLANumber pGoTLANumber) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAString pGoTLAString) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
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
