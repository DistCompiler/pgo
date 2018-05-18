package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import pgo.errors.IssueContext;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLACaseArm;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAFunctionSubstitutionPair;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAGeneralIdentifierPart;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAIdentifierOrTuple;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLASubstitutionKey;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUniversal;

public class TLAExpressionMacroSubstitutionVisitor extends PGoTLAExpressionVisitor<PGoTLAExpression, RuntimeException> {

	private IssueContext ctx;
	private Map<String, PGoTLAExpression> macroArgs;

	public TLAExpressionMacroSubstitutionVisitor(IssueContext ctx, Map<String, PGoTLAExpression> macroArgs) {
		this.ctx= ctx;
		this.macroArgs = macroArgs;
	}
	
	private List<PGoTLAGeneralIdentifierPart> substitutePrefix(List<PGoTLAGeneralIdentifierPart> prefix){
		List<PGoTLAGeneralIdentifierPart> result = new ArrayList<>();
		for(PGoTLAGeneralIdentifierPart part : prefix) {
			// TODO: what would TLC do if the identifier part's name matched an argument?
			result.add(new PGoTLAGeneralIdentifierPart(part.getLocation(), part.getIdentifier().copy(),
					part.getParameters().stream().map(p -> p.accept(this)).collect(Collectors.toList())));
		}
		return result;
	}
	
	private List<PGoTLAQuantifierBound> substituteQuantifierBounds(List<PGoTLAQuantifierBound> bounds){
		List<PGoTLAQuantifierBound> result = new ArrayList<>();
		for(PGoTLAQuantifierBound qb : bounds) {
			List<PGoTLAIdentifier> ids = substituteIdentifiers(qb.getIds());
			result.add(new PGoTLAQuantifierBound(qb.getLocation(), qb.getType(), ids, qb.getSet().accept(this)));
		}
		return result;
	}
	
	private List<PGoTLAIdentifier> substituteIdentifiers(List<PGoTLAIdentifier> ids){
		List<PGoTLAIdentifier> result = new ArrayList<>();
		for(PGoTLAIdentifier id : ids) {
			if(macroArgs.containsKey(id.getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(id));
			}
			result.add(id.copy());
		}
		return result;
	}

	@Override
	public PGoTLAExpression visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		return new PGoTLAFunctionCall(pGoTLAFunctionCall.getLocation(), pGoTLAFunctionCall.getFunction().accept(this),
				pGoTLAFunctionCall.getParams().stream().map(p -> p.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		return new PGoTLABinOp(pGoTLABinOp.getLocation(), pGoTLABinOp.getOperation(),
				substitutePrefix(pGoTLABinOp.getPrefix()), pGoTLABinOp.getLHS().accept(this),
				pGoTLABinOp.getRHS().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return pGoTLABool.copy();
	}

	@Override
	public PGoTLAExpression visit(PGoTLACase pGoTLACase) throws RuntimeException {
		return new PGoTLACase(
				pGoTLACase.getLocation(),
				pGoTLACase.getArms().stream().map( arm -> {
					return new PGoTLACaseArm(arm.getLocation(), arm.getCondition().accept(this), arm.getResult().accept(this));
					}).collect(Collectors.toList()),
				pGoTLACase.getOther() != null ? pGoTLACase.getOther().accept(this) : null);
	}

	@Override
	public PGoTLAExpression visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		return new PGoTLAExistential(pGoTLAExistential.getLocation(), substituteIdentifiers(pGoTLAExistential.getIds()),
				pGoTLAExistential.getBody().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		return new PGoTLAFunction(pGoTLAFunction.getLocation(), substituteQuantifierBounds(pGoTLAFunction.getArguments()),
				pGoTLAFunction.getBody().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		return new PGoTLAFunctionSet(pGoTLAFunctionSet.getLocation(), pGoTLAFunctionSet.getFrom().accept(this), pGoTLAFunctionSet.getTo().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		return new PGoTLAFunctionSubstitution(
				pGoTLAFunctionSubstitution.getLocation(),
				pGoTLAFunctionSubstitution.getSource().accept(this),
				pGoTLAFunctionSubstitution.getSubstitutions().stream().map(pair -> {
					return new PGoTLAFunctionSubstitutionPair(
							pair.getLocation(),
							pair.getKeys().stream().map(PGoTLASubstitutionKey::copy).collect(Collectors.toList()),
							pair.getValue().accept(this));
				}).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		return new PGoTLAIf(pGoTLAIf.getLocation(), pGoTLAIf.getCond().accept(this), pGoTLAIf.getTval().accept(this), pGoTLAIf.getFval().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLALet pGoTLALet) throws RuntimeException {
		return new PGoTLALet(pGoTLALet.getLocation(), null, pGoTLALet.getBody().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		if(pGoTLAVariable.getGeneralIdentifierPrefix().isEmpty()) {
			if(macroArgs.containsKey(pGoTLAVariable.getName().getId())) {
				return macroArgs.get(pGoTLAVariable.getName().getId()).copy();
			}
		}else {
			if(macroArgs.containsKey(pGoTLAVariable.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(pGoTLAVariable.getName()));
			}
		}
		return new PGoTLAGeneralIdentifier(pGoTLAVariable.getLocation(), pGoTLAVariable.getName().copy(),
				substitutePrefix(pGoTLAVariable.getGeneralIdentifierPrefix()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		return new PGoTLATuple(pGoTLATuple.getLocation(), pGoTLATuple.getElements().stream().map(e -> e.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		return new PGoTLAMaybeAction(pGoTLAMaybeAction.getLocation(), pGoTLAMaybeAction.getBody().accept(this), pGoTLAMaybeAction.getVars().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		return pGoTLANumber.copy();
	}

	@Override
	public PGoTLAExpression visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		if(macroArgs.containsKey(pGoTLAOperatorCall.getName().getId())) {
			ctx.error(new MacroArgumentInnerScopeConflictIssue(pGoTLAOperatorCall.getName()));
		}
		return new PGoTLAOperatorCall(pGoTLAOperatorCall.getLocation(),
				pGoTLAOperatorCall.getName().copy(),
				substitutePrefix(pGoTLAOperatorCall.getPrefix()),
				pGoTLAOperatorCall.getArgs().stream().map(a -> a.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		return new PGoTLAQuantifiedExistential(pGoTLAQuantifiedExistential.getLocation(),
				substituteQuantifierBounds(pGoTLAQuantifiedExistential.getIds()),
				pGoTLAQuantifiedExistential.getBody().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		return new PGoTLAQuantifiedExistential(pGoTLAQuantifiedUniversal.getLocation(),
				substituteQuantifierBounds(pGoTLAQuantifiedUniversal.getIds()),
				pGoTLAQuantifiedUniversal.getBody().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		return new PGoTLARecordConstructor(pGoTLARecordConstructor.getLocation(), pGoTLARecordConstructor.getFields().stream().map( field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new PGoTLARecordConstructor.Field(field.getLocation(), field.getName().copy(), field.getValue().accept(this));
		}).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		return new PGoTLARecordSet(pGoTLARecordSet.getLocation(), pGoTLARecordSet.getFields().stream().map( field -> {
			if(macroArgs.containsKey(field.getName().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(field.getName()));
			}
			return new PGoTLARecordSet.Field(field.getLocation(), field.getName().copy(), field.getSet().accept(this));
		}).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		return new PGoTLARequiredAction(
				pGoTLARequiredAction.getLocation(),
				pGoTLARequiredAction.getBody().accept(this),
				pGoTLARequiredAction.getVars().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		return new PGoTLASetConstructor(pGoTLASetConstructor.getLocation(),
				pGoTLASetConstructor.getContents().stream().map(c -> c.accept(this)).collect(Collectors.toList()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		return new PGoTLASetComprehension(pGoTLASetComprehension.getLocation(),
				pGoTLASetComprehension.getBody().accept(this), substituteQuantifierBounds(pGoTLASetComprehension.getBounds()));
	}

	@Override
	public PGoTLAExpression visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		PGoTLAIdentifierOrTuple ident = pGoTLASetRefinement.getIdent();
		if(ident.isTuple()) {
			substituteIdentifiers(ident.getTuple());
		}else {
			if(macroArgs.containsKey(ident.getId().getId())) {
				ctx.error(new MacroArgumentInnerScopeConflictIssue(ident.getId()));
			}
		}
		return new PGoTLASetRefinement(pGoTLASetRefinement.getLocation(), pGoTLASetRefinement.getIdent().copy(),
				pGoTLASetRefinement.getFrom().accept(this), pGoTLASetRefinement.getWhen().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAString pGoTLAString) throws RuntimeException {
		return pGoTLAString.copy();
	}

	@Override
	public PGoTLAExpression visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		return new PGoTLAUnary(pGoTLAUnary.getLocation(), pGoTLAUnary.getOperation(), substitutePrefix(pGoTLAUnary.getPrefix()),
				pGoTLAUnary.getOperand().accept(this));
	}

	@Override
	public PGoTLAExpression visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		return new PGoTLAUniversal(pGoTLAUniversal.getLocation(), substituteIdentifiers(pGoTLAUniversal.getIds()), pGoTLAUniversal.getBody().accept(this));
	}

	

}
