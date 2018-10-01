package pgo.trans.passes.validation;

import pgo.TODO;
import pgo.errors.IssueContext;
import pgo.model.tla.*;
import pgo.trans.intermediate.DanglingReferenceIssue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ExpressionVariableAccessValidationVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	private final IssueContext ctx;
	private final Set<String> macrosInScope;
	private final Set<String> proceduresInScope;
	private final Set<String> variablesInScope;
	private final Set<String> refVariablesInScope;

	public ExpressionVariableAccessValidationVisitor(IssueContext ctx, Set<String> macrosInScope,
	                                                 Set<String> proceduresInScope, Set<String> variablesInScope,
	                                                 Set<String> refVariablesInScope) {
		this.ctx = ctx;
		this.macrosInScope = macrosInScope;
		this.proceduresInScope = proceduresInScope;
		this.variablesInScope = variablesInScope;
		this.refVariablesInScope = refVariablesInScope;
	}

	private void validateBoundsAndBody(List<TLAQuantifierBound> bounds, TLAExpression body) {
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		Set<String> localVariablesInScope = new HashSet<>(variablesInScope);
		Set<String> localRefVariablesInScope = new HashSet<>(refVariablesInScope);
		for (TLAQuantifierBound bound : bounds) {
			bound.getSet().accept(new ExpressionVariableAccessValidationVisitor(
					ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
			for (TLAIdentifier identifier : bound.getIds()) {
				String name = identifier.getId();
				localVariablesInScope.add(name);
				localRefVariablesInScope.remove(name);
				localMacrosInScope.remove(name);
				localProceduresInScope.remove(name);
			}
		}
		body.accept(new ExpressionVariableAccessValidationVisitor(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
	}

	private void validateIdsAndBody(List<TLAIdentifier> identifiers, TLAExpression body) {
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		Set<String> localVariablesInScope = new HashSet<>(variablesInScope);
		Set<String> localRefVariablesInScope = new HashSet<>(refVariablesInScope);
		for (TLAIdentifier identifier : identifiers) {
			String name = identifier.getId();
			localVariablesInScope.add(name);
			localRefVariablesInScope.remove(name);
			localMacrosInScope.remove(name);
			localProceduresInScope.remove(name);
		}
		body.accept(new ExpressionVariableAccessValidationVisitor(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
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
		TLACase.getArms().forEach(a -> {
			a.getCondition().accept(this);
			a.getResult().accept(this);
		});
		TLACase.getOther().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential TLAExistential) throws RuntimeException {
		validateIdsAndBody(TLAExistential.getIds(), TLAExistential.getBody());
		return null;
	}

	@Override
	public Void visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		validateBoundsAndBody(pGoTLAFunction.getArguments(), pGoTLAFunction.getBody());
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
		pGoTLAFunctionSubstitution.getSource().accept(this);
		for (TLAFunctionSubstitutionPair substitution : pGoTLAFunctionSubstitution.getSubstitutions()) {
			substitution.getKeys().forEach(key -> key.getIndices().forEach(i -> i.accept(this)));
			substitution.getValue().accept(this);
		}
		return null;
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
		throw new TODO();
	}

	@Override
	public Void visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		if (pGoTLAVariable.getGeneralIdentifierPrefix().size() != 0) {
			throw new TODO();
		}
		if (!variablesInScope.contains(pGoTLAVariable.getName().getId()) &&
				!refVariablesInScope.contains(pGoTLAVariable.getName().getId())) {
			ctx.error(new DanglingReferenceIssue(pGoTLAVariable.getUID()));
		}
		return null;
	}

	@Override
	public Void visit(TLATuple pGoTLATuple) throws RuntimeException {
		pGoTLATuple.getElements().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		pGoTLAMaybeAction.getVars().accept(this);
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
		// TODO validate operator name
		pGoTLAOperatorCall.getArgs().forEach(a -> a.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		validateBoundsAndBody(pGoTLAQuantifiedExistential.getIds(), pGoTLAQuantifiedExistential.getBody());
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		validateBoundsAndBody(pGoTLAQuantifiedUniversal.getIds(), pGoTLAQuantifiedUniversal.getBody());
		return null;
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
		pGoTLARequiredAction.getVars().accept(this);
		pGoTLARequiredAction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		pGoTLASetConstructor.getContents().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		validateBoundsAndBody(pGoTLASetComprehension.getBounds(), pGoTLASetComprehension.getBody());
		return null;
	}

	@Override
	public Void visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		Set<String> localVariablesInScope = new HashSet<>(variablesInScope);
		Set<String> localRefVariablesInScope = new HashSet<>(refVariablesInScope);
		if (pGoTLASetRefinement.getIdent().isTuple()) {
			for (TLAIdentifier identifier : pGoTLASetRefinement.getIdent().getTuple()) {
				String name = identifier.getId();
				localVariablesInScope.add(name);
				localRefVariablesInScope.remove(name);
				localMacrosInScope.remove(name);
				localProceduresInScope.remove(name);
			}
		} else {
			String name = pGoTLASetRefinement.getIdent().getId().getId();
			localVariablesInScope.add(name);
			localRefVariablesInScope.remove(name);
			localMacrosInScope.remove(name);
			localProceduresInScope.remove(name);
		}
		pGoTLASetRefinement.getWhen().accept(new ExpressionVariableAccessValidationVisitor(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
		return null;
	}

	@Override
	public Void visit(TLAString pGoTLAString) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		// TODO validate operation
		pGoTLAUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		validateIdsAndBody(pGoTLAUniversal.getIds(), pGoTLAUniversal.getBody());
		return null;
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAFairness tlaFairness) throws RuntimeException {
		tlaFairness.getVars().accept(this);
		tlaFairness.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		if (!refVariablesInScope.contains(tlaRef.getTarget())) {
			ctx.error(new DanglingReferenceIssue(tlaRef.getUID()));
		}
		return null;
	}
}
