package pgo.trans.passes.validation;

import pgo.TODO;
import pgo.model.tla.*;

import java.util.List;

public class NonModularPlusCalTLAExpressionValidationVisitor extends TLAExpressionVisitor<Boolean, RuntimeException> {
	private boolean validateExpressions(List<TLAExpression> expressions) {
		return expressions.stream().allMatch(e -> e.accept(this));
	}

	private boolean validateBounds(List<TLAQuantifierBound> bounds) {
		return bounds.stream().allMatch(b -> b.getSet().accept(this));
	}

	@Override
	public Boolean visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		return tlaFunctionCall.getFunction().accept(this) && validateExpressions(tlaFunctionCall.getParams());
	}

	@Override
	public Boolean visit(TLABinOp tlaBinOp) throws RuntimeException {
		return tlaBinOp.getLHS().accept(this) && tlaBinOp.getRHS().accept(this);
	}

	@Override
	public Boolean visit(TLABool tlaBool) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLACase tlaCase) throws RuntimeException {
		return tlaCase.getArms()
				.stream()
				.allMatch(a -> a.getCondition().accept(this) && a.getResult().accept(this)) &&
				(tlaCase.getOther() == null || tlaCase.getOther().accept(this));
	}

	@Override
	public Boolean visit(TLADot tlaDot) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Boolean visit(TLAExistential tlaExistential) throws RuntimeException {
		return tlaExistential.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAFunction tlaFunction) throws RuntimeException {
		return validateBounds(tlaFunction.getArguments()) && tlaFunction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		return tlaFunctionSet.getFrom().accept(this) && tlaFunctionSet.getTo().accept(this);
	}

	@Override
	public Boolean visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		return tlaFunctionSubstitution.getSource().accept(this) &&
				tlaFunctionSubstitution.getSubstitutions()
						.stream()
						.allMatch(
								p -> p.getValue().accept(this) &&
										p.getKeys().stream().allMatch(k -> validateExpressions(k.getIndices())));
	}

	@Override
	public Boolean visit(TLAIf tlaIf) throws RuntimeException {
		return tlaIf.getCond().accept(this) && tlaIf.getTval().accept(this) && tlaIf.getFval().accept(this);
	}

	@Override
	public Boolean visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Boolean visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLATuple tlaTuple) throws RuntimeException {
		return validateExpressions(tlaTuple.getElements());
	}

	@Override
	public Boolean visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		return tlaMaybeAction.getVars().accept(this) && tlaMaybeAction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLANumber tlaNumber) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		return validateExpressions(tlaOperatorCall.getArgs());
	}

	@Override
	public Boolean visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		return validateBounds(tlaQuantifiedExistential.getIds()) && tlaQuantifiedExistential.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return validateBounds(tlaQuantifiedUniversal.getIds()) && tlaQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		return tlaRecordConstructor.getFields().stream().allMatch(f -> f.getValue().accept(this));
	}

	@Override
	public Boolean visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		return tlaRecordSet.getFields().stream().allMatch(f -> f.getSet().accept(this));
	}

	@Override
	public Boolean visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return tlaRequiredAction.getVars().accept(this) && tlaRequiredAction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		return validateExpressions(tlaSetConstructor.getContents());
	}

	@Override
	public Boolean visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		return validateBounds(tlaSetComprehension.getBounds()) && tlaSetComprehension.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		return tlaSetRefinement.getFrom().accept(this) && tlaSetRefinement.getWhen().accept(this);
	}

	@Override
	public Boolean visit(TLAString tlaString) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLAUnary tlaUnary) throws RuntimeException {
		return tlaUnary.getOperand().accept(this);
	}

	@Override
	public Boolean visit(TLAUniversal tlaUniversal) throws RuntimeException {
		return tlaUniversal.getBody().accept(this);
	}

	@Override
	public Boolean visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLAFairness tlaFairness) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(TLARef tlaRef) throws RuntimeException {
		return false;
	}
}
