package pgo.trans.intermediate;

import pgo.TODO;
import pgo.errors.IssueContext;
import pgo.model.tla.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class TLAExpressionMacroSubstitutionVisitor extends TLAExpressionVisitor<TLAExpression, RuntimeException> {

	private IssueContext ctx;
	private Map<String, TLAExpression> macroArgs;

	public TLAExpressionMacroSubstitutionVisitor(IssueContext ctx, Map<String, TLAExpression> macroArgs) {
		this.ctx= ctx;
		this.macroArgs = macroArgs;
	}
	
	private List<TLAGeneralIdentifierPart> substitutePrefix(List<TLAGeneralIdentifierPart> prefix){
		List<TLAGeneralIdentifierPart> result = new ArrayList<>();
		for(TLAGeneralIdentifierPart part : prefix) {
			// TODO: what would TLC do if the identifier part's name matched an argument?
			result.add(new TLAGeneralIdentifierPart(part.getLocation(), part.getIdentifier().copy(),
					part.getParameters().stream().map(p -> p.accept(this)).collect(Collectors.toList())));
		}
		return result;
	}
	
	private List<TLAQuantifierBound> substituteQuantifierBounds(List<TLAQuantifierBound> bounds){
		List<TLAQuantifierBound> result = new ArrayList<>();
		for(TLAQuantifierBound qb : bounds) {
			List<TLAIdentifier> ids = substituteIdentifiers(qb.getIds());
			result.add(new TLAQuantifierBound(qb.getLocation(), qb.getType(), ids, qb.getSet().accept(this)));
		}
		return result;
	}
	
	private List<TLAIdentifier> substituteIdentifiers(List<TLAIdentifier> ids){
		List<TLAIdentifier> result = new ArrayList<>();
		for(TLAIdentifier id : ids) {
			if(macroArgs.containsKey(id.getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(id));
			}
			result.add(id.copy());
		}
		return result;
	}

	@Override
	public TLAExpression visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		return new TLAFunctionCall(pGoTLAFunctionCall.getLocation(), pGoTLAFunctionCall.getFunction().accept(this),
				pGoTLAFunctionCall.getParams().stream().map(p -> p.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLABinOp TLABinOp) throws RuntimeException {
		return new TLABinOp(TLABinOp.getLocation(), TLABinOp.getOperation(),
				substitutePrefix(TLABinOp.getPrefix()), TLABinOp.getLHS().accept(this),
				TLABinOp.getRHS().accept(this));
	}

	@Override
	public TLAExpression visit(TLABool TLABool) throws RuntimeException {
		return TLABool.copy();
	}

	@Override
	public TLAExpression visit(TLACase TLACase) throws RuntimeException {
		return new TLACase(
				TLACase.getLocation(),
				TLACase.getArms().stream().map(arm -> {
					return new TLACaseArm(arm.getLocation(), arm.getCondition().accept(this), arm.getResult().accept(this));
					}).collect(Collectors.toList()),
				TLACase.getOther() != null ? TLACase.getOther().accept(this) : null);
	}

	@Override
	public TLAExpression visit(TLAExistential TLAExistential) throws RuntimeException {
		return new TLAExistential(TLAExistential.getLocation(), substituteIdentifiers(TLAExistential.getIds()),
				TLAExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		return new TLAFunction(pGoTLAFunction.getLocation(), substituteQuantifierBounds(pGoTLAFunction.getArguments()),
				pGoTLAFunction.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		return new TLAFunctionSet(pGoTLAFunctionSet.getLocation(), pGoTLAFunctionSet.getFrom().accept(this), pGoTLAFunctionSet.getTo().accept(this));
	}

	@Override
	public TLAExpression visit(TLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		return new TLAFunctionSubstitution(
				pGoTLAFunctionSubstitution.getLocation(),
				pGoTLAFunctionSubstitution.getSource().accept(this),
				pGoTLAFunctionSubstitution.getSubstitutions().stream().map(pair -> {
					return new TLAFunctionSubstitutionPair(
							pair.getLocation(),
							pair.getKeys().stream().map(TLASubstitutionKey::copy).collect(Collectors.toList()),
							pair.getValue().accept(this));
				}).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLAIf pGoTLAIf) throws RuntimeException {
		return new TLAIf(pGoTLAIf.getLocation(), pGoTLAIf.getCond().accept(this), pGoTLAIf.getTval().accept(this), pGoTLAIf.getFval().accept(this));
	}

	@Override
	public TLAExpression visit(TLALet pGoTLALet) throws RuntimeException {
		return new TLALet(pGoTLALet.getLocation(), null, pGoTLALet.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		if(pGoTLAVariable.getGeneralIdentifierPrefix().isEmpty()) {
			if(macroArgs.containsKey(pGoTLAVariable.getName().getId())) {
				return macroArgs.get(pGoTLAVariable.getName().getId()).copy();
			}
		}else {
			if(macroArgs.containsKey(pGoTLAVariable.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(pGoTLAVariable.getName()));
			}
		}
		return new TLAGeneralIdentifier(pGoTLAVariable.getLocation(), pGoTLAVariable.getName().copy(),
				substitutePrefix(pGoTLAVariable.getGeneralIdentifierPrefix()));
	}

	@Override
	public TLAExpression visit(TLATuple pGoTLATuple) throws RuntimeException {
		return new TLATuple(pGoTLATuple.getLocation(), pGoTLATuple.getElements().stream().map(e -> e.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		return new TLAMaybeAction(pGoTLAMaybeAction.getLocation(), pGoTLAMaybeAction.getBody().accept(this), pGoTLAMaybeAction.getVars().accept(this));
	}

	@Override
	public TLAExpression visit(TLANumber pGoTLANumber) throws RuntimeException {
		return pGoTLANumber.copy();
	}

	@Override
	public TLAExpression visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		if(macroArgs.containsKey(pGoTLAOperatorCall.getName().getId())) {
			ctx.error(new MacroArgumentInnerScopeConflictIssue(pGoTLAOperatorCall.getName()));
		}
		return new TLAOperatorCall(pGoTLAOperatorCall.getLocation(),
				pGoTLAOperatorCall.getName().copy(),
				substitutePrefix(pGoTLAOperatorCall.getPrefix()),
				pGoTLAOperatorCall.getArgs().stream().map(a -> a.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		return new TLAQuantifiedExistential(pGoTLAQuantifiedExistential.getLocation(),
				substituteQuantifierBounds(pGoTLAQuantifiedExistential.getIds()),
				pGoTLAQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return new TLAQuantifiedUniversal(pGoTLAQuantifiedUniversal.getLocation(),
				substituteQuantifierBounds(pGoTLAQuantifiedUniversal.getIds()),
				pGoTLAQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		return new TLARecordConstructor(pGoTLARecordConstructor.getLocation(), pGoTLARecordConstructor.getFields().stream().map(field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new TLARecordConstructor.Field(field.getLocation(), field.getName().copy(), field.getValue().accept(this));
		}).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		return new TLARecordSet(pGoTLARecordSet.getLocation(), pGoTLARecordSet.getFields().stream().map(field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new TLARecordSet.Field(field.getLocation(), field.getName().copy(), field.getSet().accept(this));
		}).collect(Collectors.toList()));
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
		return new TLASetConstructor(pGoTLASetConstructor.getLocation(),
				pGoTLASetConstructor.getContents().stream().map(c -> c.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public TLAExpression visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		return new TLASetComprehension(pGoTLASetComprehension.getLocation(),
				pGoTLASetComprehension.getBody().accept(this), substituteQuantifierBounds(pGoTLASetComprehension.getBounds()));
	}

	@Override
	public TLAExpression visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		TLAIdentifierOrTuple ident = pGoTLASetRefinement.getIdent();
		if(ident.isTuple()) {
			substituteIdentifiers(ident.getTuple());
		}else {
			if(macroArgs.containsKey(ident.getId().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(ident.getId()));
			}
		}
		return new TLASetRefinement(pGoTLASetRefinement.getLocation(), pGoTLASetRefinement.getIdent().copy(),
				pGoTLASetRefinement.getFrom().accept(this), pGoTLASetRefinement.getWhen().accept(this));
	}

	@Override
	public TLAExpression visit(TLAString pGoTLAString) throws RuntimeException {
		return pGoTLAString.copy();
	}

	@Override
	public TLAExpression visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		return new TLAUnary(pGoTLAUnary.getLocation(), pGoTLAUnary.getOperation(), substitutePrefix(pGoTLAUnary.getPrefix()),
				pGoTLAUnary.getOperand().accept(this));
	}

	@Override
	public TLAExpression visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		return new TLAUniversal(pGoTLAUniversal.getLocation(), substituteIdentifiers(pGoTLAUniversal.getIds()), pGoTLAUniversal.getBody().accept(this));
	}

	@Override
	public TLAExpression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		return plusCalDefaultInitValue.copy();
	}

	@Override
	public TLAExpression visit(TLAFairness fairness) throws RuntimeException {
		return new TLAFairness(
				fairness.getLocation(), fairness.getType(), fairness.getVars().accept(this),
				fairness.getExpression().accept(this));
	}

	@Override
	public TLAExpression visit(TLASpecialVariableOld tlaSpecialVariableOld) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public TLAExpression visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new TODO();
	}

}
