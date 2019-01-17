package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.tla.*;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.passes.codegen.TemporaryBinding;

import java.util.ArrayList;
import java.util.List;

public class TLAExpressionMappingMacroReadExpansionVisitor
		extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final TemporaryBinding temporaryBinding;
	private final TLAExpression dollarVariable;

	public TLAExpressionMappingMacroReadExpansionVisitor(DefinitionRegistry registry, TemporaryBinding temporaryBinding,
	                                                     TLAExpression dollarVariable) {
		this.registry = registry;
		this.temporaryBinding = temporaryBinding;
		this.dollarVariable = dollarVariable;
	}

	private List<TLAExpression> substituteExpressions(List<TLAExpression> expressions) {
		List<TLAExpression> result = new ArrayList<>();
		for (TLAExpression expression : expressions) {
			result.add(expression.accept(this));
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		return new TLAFunctionCall(
				tlaFunctionCall.getLocation(),
				tlaFunctionCall.getFunction().accept(this),
				substituteExpressions(tlaFunctionCall.getParams()));
	}

	@Override
	public TLAExpression visit(TLABinOp tlaBinOp) throws RuntimeException {
		TLAExpression lhs = tlaBinOp.getLHS().accept(this);
		TLAExpression rhs = tlaBinOp.getRHS().accept(this);
		return new TLABinOp(tlaBinOp.getLocation(), tlaBinOp.getOperation(), tlaBinOp.getPrefix(), lhs, rhs);
	}

	@Override
	public TLAExpression visit(TLABool tlaBool) throws RuntimeException {
		return new TLABool(tlaBool.getLocation(), tlaBool.getValue());
	}

	@Override
	public TLAExpression visit(TLACase tlaCase) throws RuntimeException {
		List<TLACaseArm> arms = new ArrayList<>();
		for (TLACaseArm arm : tlaCase.getArms()) {
			arms.add(new TLACaseArm(
					arm.getLocation(),arm.getCondition().accept(this), arm.getResult().accept(this)));
		}
		return new TLACase(tlaCase.getLocation(), arms, tlaCase.getOther().accept(this));
	}

	@Override
	public TLAExpression visit(TLAExistential tlaExistential) throws RuntimeException {
		return new TLAExistential(
				tlaExistential.getLocation(),
				tlaExistential.getIds(),
				tlaExistential.getBody().accept(this));
	}

	private List<TLAQuantifierBound> processQuantifierBounds(List<TLAQuantifierBound> bounds) {
		List<TLAQuantifierBound> result = new ArrayList<>();
		for (TLAQuantifierBound bound : bounds) {
			bounds.add(new TLAQuantifierBound(
					bound.getLocation(),
					bound.getType(),
					bound.getIds(),
					bound.getSet().accept(this)));
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAFunction tlaFunction) throws RuntimeException {
		List<TLAQuantifierBound> bounds = processQuantifierBounds(tlaFunction.getArguments());
		return new TLAFunction(tlaFunction.getLocation(), bounds, tlaFunction.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		return new TLAFunctionSet(
				tlaFunctionSet.getLocation(),
				tlaFunctionSet.getFrom().accept(this),
				tlaFunctionSet.getTo().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		List<TLAFunctionSubstitutionPair> pairs = new ArrayList<>();
		for (TLAFunctionSubstitutionPair substitution : tlaFunctionSubstitution.getSubstitutions()) {
			List<TLASubstitutionKey> keys = new ArrayList<>();
			for (TLASubstitutionKey key : substitution.getKeys()) {
				keys.add(new TLASubstitutionKey(key.getLocation(), substituteExpressions(key.getIndices())));
			}
			pairs.add(new TLAFunctionSubstitutionPair(
					substitution.getLocation(),
					keys,
					substitution.getValue().accept(this)));
		}
		return new TLAFunctionSubstitution(
				tlaFunctionSubstitution.getLocation(),
				tlaFunctionSubstitution.getSource().accept(this),
				pairs);
	}

	@Override
	public TLAExpression visit(TLAIf tlaIf) throws RuntimeException {
		return new TLAIf(
				tlaIf.getLocation(),
				tlaIf.getCond().accept(this),
				tlaIf.getTval().accept(this),
				tlaIf.getFval().accept(this));
	}

	@Override
	public TLAExpression visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		return temporaryBinding
				.lookup(registry.followReference(tlaGeneralIdentifier.getUID()))
				.orElse(tlaGeneralIdentifier);
	}

	@Override
	public TLAExpression visit(TLATuple tlaTuple) throws RuntimeException {
		return new TLATuple(tlaTuple.getLocation(), substituteExpressions(tlaTuple.getElements()));
	}

	@Override
	public TLAExpression visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		return new TLAMaybeAction(
				tlaMaybeAction.getLocation(),
				tlaMaybeAction.getBody().accept(this),
				tlaMaybeAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLANumber tlaNumber) throws RuntimeException {
		return tlaNumber.copy();
	}

	@Override
	public TLAExpression visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		return new TLAOperatorCall(
				tlaOperatorCall.getLocation(),
				tlaOperatorCall.getName(),
				tlaOperatorCall.getPrefix(),
				substituteExpressions(tlaOperatorCall.getArgs()));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		return new TLAQuantifiedExistential(
				tlaQuantifiedExistential.getLocation(),
				processQuantifierBounds(tlaQuantifiedExistential.getIds()),
				tlaQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return new TLAQuantifiedUniversal(
				tlaQuantifiedUniversal.getLocation(),
				processQuantifierBounds(tlaQuantifiedUniversal.getIds()),
				tlaQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		List<TLARecordConstructor.Field> fields = new ArrayList<>();
		for (TLARecordConstructor.Field field : tlaRecordConstructor.getFields()) {
			fields.add(new TLARecordConstructor.Field(
					field.getLocation(),
					field.getName(),
					field.getValue().accept(this)));
		}
		return new TLARecordConstructor(tlaRecordConstructor.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		List<TLARecordSet.Field> fields = new ArrayList<>();
		for (TLARecordSet.Field field : tlaRecordSet.getFields()) {
			fields.add(new TLARecordSet.Field(field.getLocation(), field.getName(), field.getSet().accept(this)));
		}
		return new TLARecordSet(tlaRecordSet.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return new TLARequiredAction(
				tlaRequiredAction.getLocation(),
				tlaRequiredAction.getBody().accept(this),
				tlaRequiredAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		return new TLASetConstructor(
				tlaSetConstructor.getLocation(),
				substituteExpressions(tlaSetConstructor.getContents()));
	}

	@Override
	public TLAExpression visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		return new TLASetComprehension(
				tlaSetComprehension.getLocation(),
				tlaSetComprehension.getBody(),
				processQuantifierBounds(tlaSetComprehension.getBounds()));
	}

	@Override
	public TLAExpression visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		return new TLASetRefinement(
				tlaSetRefinement.getLocation(),
				tlaSetRefinement.getIdent(),
				tlaSetRefinement.getFrom().accept(this),
				tlaSetRefinement.getWhen().accept(this));
	}

	@Override
	public TLAExpression visit(TLAString tlaString) throws RuntimeException {
		return tlaString.copy();
	}

	@Override
	public TLAExpression visit(TLAUnary tlaUnary) throws RuntimeException {
		return new TLAUnary(
				tlaUnary.getLocation(),
				tlaUnary.getOperation(),
				tlaUnary.getPrefix(),
				tlaUnary.getOperand().accept(this));
	}

	@Override
	public TLAExpression visit(TLAUniversal tlaUniversal) throws RuntimeException {
		return new TLAUniversal(
				tlaUniversal.getLocation(),
				tlaUniversal.getIds(),
				tlaUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue.copy();
	}

	@Override
	public TLAExpression visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		return dollarVariable;
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public TLAExpression visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
