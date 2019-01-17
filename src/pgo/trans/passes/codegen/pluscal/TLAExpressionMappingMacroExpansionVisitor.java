package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.builder.TemporaryBinding;
import pgo.model.tla.*;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

public class TLAExpressionMappingMacroExpansionVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {
	private final DefinitionRegistry registry;
	private final TemporaryBinding temporaryBinding;
	private final Supplier<TLAGeneralIdentifier> dollarVariable;
	private final Supplier<TLAExpression> dollarValue;

	public TLAExpressionMappingMacroExpansionVisitor(DefinitionRegistry registry,
	                                                 TemporaryBinding temporaryBinding,
	                                                 Supplier<TLAGeneralIdentifier> dollarVariable,
	                                                 Supplier<TLAExpression> dollarValue) {
		this.registry = registry;
		this.temporaryBinding = temporaryBinding;
		this.dollarVariable = dollarVariable;
		this.dollarValue = dollarValue;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : pGoTLAFunctionCall.getParams()) {
			arguments.add(argument.accept(this));
		}
		return new TLAFunctionCall(pGoTLAFunctionCall.getLocation(), pGoTLAFunctionCall.getFunction(), arguments);
	}

	@Override
	public TLAExpression visit(TLABinOp TLABinOp) throws RuntimeException {
		TLAExpression lhs = TLABinOp.getLHS().accept(this);
		TLAExpression rhs = TLABinOp.getRHS().accept(this);
		return new TLABinOp(TLABinOp.getLocation(), TLABinOp.getOperation(), TLABinOp.getPrefix(), lhs, rhs);
	}

	@Override
	public TLAExpression visit(TLABool TLABool) throws RuntimeException {
		return TLABool;
	}

	@Override
	public TLAExpression visit(TLACase TLACase) throws RuntimeException {
		List<TLACaseArm> transformedArm = new ArrayList<>();
		for (TLACaseArm arm : TLACase.getArms()) {
			TLAExpression condition = arm.getCondition().accept(this);
			TLAExpression result = arm.getResult().accept(this);
			transformedArm.add(new TLACaseArm(arm.getLocation(), condition, result));
		}
		return new TLACase(TLACase.getLocation(), transformedArm, TLACase.getOther().accept(this));
	}

	@Override
	public TLAExpression visit(TLAExistential TLAExistential) throws RuntimeException {
		return new TLAExistential(
				TLAExistential.getLocation(),
				TLAExistential.getIds(),
				TLAExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		return new TLAFunction(
				pGoTLAFunction.getLocation(), pGoTLAFunction.getArguments(), pGoTLAFunction.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		return new TLAFunctionSet(
				pGoTLAFunctionSet.getLocation(),
				pGoTLAFunctionSet.getFrom().accept(this),
				pGoTLAFunctionSet.getTo().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		List<TLAFunctionSubstitutionPair> pairs = new ArrayList<>();
		for (TLAFunctionSubstitutionPair substitution : pGoTLAFunctionSubstitution.getSubstitutions()) {
			List<TLASubstitutionKey> keys = new ArrayList<>();
			for (TLASubstitutionKey key : substitution.getKeys()) {
				List<TLAExpression> indices = new ArrayList<>();
				for (TLAExpression index : key.getIndices()) {
					indices.add(index.accept(this));
				}
				keys.add(new TLASubstitutionKey(key.getLocation(), indices));
			}
			pairs.add(new TLAFunctionSubstitutionPair(
					substitution.getLocation(),
					keys,
					substitution.getValue().accept(this)));
		}
		return new TLAFunctionSubstitution(
				pGoTLAFunctionSubstitution.getLocation(),
				pGoTLAFunctionSubstitution.getSource().accept(this),
				pairs);
	}

	@Override
	public TLAExpression visit(TLAIf pGoTLAIf) throws RuntimeException {
		return new TLAIf(
				pGoTLAIf.getLocation(),
				pGoTLAIf.getCond().accept(this),
				pGoTLAIf.getTval().accept(this),
				pGoTLAIf.getFval().accept(this));
	}

	@Override
	public TLAExpression visit(TLALet pGoTLALet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		return temporaryBinding.lookup(registry.followReference(pGoTLAVariable.getUID())).orElse(pGoTLAVariable);
	}

	@Override
	public TLAExpression visit(TLATuple pGoTLATuple) throws RuntimeException {
		List<TLAExpression> elements = new ArrayList<>();
		for (TLAExpression expression : pGoTLATuple.getElements()) {
			elements.add(expression.accept(this));
		}
		return new TLATuple(pGoTLATuple.getLocation(), elements);
	}

	@Override
	public TLAExpression visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		return new TLAMaybeAction(
				pGoTLAMaybeAction.getLocation(),
				pGoTLAMaybeAction.getBody().accept(this),
				pGoTLAMaybeAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLANumber pGoTLANumber) throws RuntimeException {
		return pGoTLANumber;
	}

	@Override
	public TLAExpression visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		List<TLAExpression> arguments = new ArrayList<>();
		for (TLAExpression argument : pGoTLAOperatorCall.getArgs()) {
			arguments.add(argument.accept(this));
		}
		return new TLAOperatorCall(
				pGoTLAOperatorCall.getLocation(),
				pGoTLAOperatorCall.getName(),
				pGoTLAOperatorCall.getPrefix(),
				arguments);
	}

	private List<TLAQuantifierBound> transformBounds(List<TLAQuantifierBound> bounds) {
		List<TLAQuantifierBound> result = new ArrayList<>();
		for (TLAQuantifierBound bound : bounds) {
			result.add(new TLAQuantifierBound(
					bound.getLocation(),
					bound.getType(),
					bound.getIds(),
					bound.getSet().accept(this)));
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		return new TLAQuantifiedExistential(
				pGoTLAQuantifiedExistential.getLocation(),
				transformBounds(pGoTLAQuantifiedExistential.getIds()),
				pGoTLAQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return new TLAQuantifiedUniversal(
				pGoTLAQuantifiedUniversal.getLocation(),
				transformBounds(pGoTLAQuantifiedUniversal.getIds()),
				pGoTLAQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		List<TLARecordConstructor.Field> fields = new ArrayList<>();
		for (TLARecordConstructor.Field field : pGoTLARecordConstructor.getFields()) {
			fields.add(new TLARecordConstructor.Field(
					field.getLocation(), field.getName(), field.getValue().accept(this)));
		}
		return new TLARecordConstructor(pGoTLARecordConstructor.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		List<TLARecordSet.Field> fields = new ArrayList<>();
		for (TLARecordSet.Field field : pGoTLARecordSet.getFields()) {
			fields.add(new TLARecordSet.Field(field.getLocation(), field.getName(), field.getSet().accept(this)));
		}
		return new TLARecordSet(pGoTLARecordSet.getLocation(), fields);
	}

	@Override
	public TLAExpression visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		return new TLARequiredAction(
				pGoTLARequiredAction.getLocation(),
				pGoTLARequiredAction.getBody().accept(this),
				pGoTLARequiredAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		List<TLAExpression> contents = new ArrayList<>();
		for (TLAExpression expression : pGoTLASetConstructor.getContents()) {
			contents.add(expression.accept(this));
		}
		return new TLASetConstructor(pGoTLASetConstructor.getLocation(), contents);
	}

	@Override
	public TLAExpression visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		return new TLASetComprehension(
				pGoTLASetComprehension.getLocation(),
				pGoTLASetComprehension.getBody().accept(this),
				transformBounds(pGoTLASetComprehension.getBounds()));
	}

	@Override
	public TLAExpression visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		return new TLASetRefinement(
				pGoTLASetRefinement.getLocation(),
				pGoTLASetRefinement.getIdent(),
				pGoTLASetRefinement.getFrom().accept(this),
				pGoTLASetRefinement.getWhen().accept(this));
	}

	@Override
	public TLAExpression visit(TLAString pGoTLAString) throws RuntimeException {
		return pGoTLAString;
	}

	@Override
	public TLAExpression visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		TLAExpression expression = pGoTLAUnary.getOperand().accept(this);
		return new TLAUnary(pGoTLAUnary.getLocation(), pGoTLAUnary.getOperation(), pGoTLAUnary.getPrefix(), expression);
	}

	@Override
	public TLAExpression visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		return new TLAUniversal(
				pGoTLAUniversal.getLocation(),
				pGoTLAUniversal.getIds(),
				pGoTLAUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue;
	}

	@Override
	public TLAExpression visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		return dollarVariable.get();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		return dollarValue.get().accept(this);
	}

	@Override
	public TLAExpression visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
