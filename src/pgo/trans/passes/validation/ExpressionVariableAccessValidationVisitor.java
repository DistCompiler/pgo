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
	public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		tlaFunctionCall.getFunction().accept(this);
		tlaFunctionCall.getParams().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLABinOp tlaBinOp) throws RuntimeException {
		tlaBinOp.getLHS().accept(this);
		tlaBinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(TLABool tlaBool) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLACase tlaCase) throws RuntimeException {
		tlaCase.getArms().forEach(a -> {
			a.getCondition().accept(this);
			a.getResult().accept(this);
		});
		tlaCase.getOther().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws RuntimeException {
		validateIdsAndBody(tlaExistential.getIds(), tlaExistential.getBody());
		return null;
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws RuntimeException {
		validateBoundsAndBody(tlaFunction.getArguments(), tlaFunction.getBody());
		return null;
	}

	@Override
	public Void visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		tlaFunctionSet.getFrom().accept(this);
		tlaFunctionSet.getTo().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		tlaFunctionSubstitution.getSource().accept(this);
		for (TLAFunctionSubstitutionPair substitution : tlaFunctionSubstitution.getSubstitutions()) {
			substitution.getKeys().forEach(key -> key.getIndices().forEach(i -> i.accept(this)));
			substitution.getValue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAIf tlaIf) throws RuntimeException {
		tlaIf.getCond().accept(this);
		tlaIf.getTval().accept(this);
		tlaIf.getFval().accept(this);
		return null;
	}

	@Override
	public Void visit(TLALet tlaLet) throws RuntimeException {
		throw new TODO();
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		if (tlaGeneralIdentifier.getGeneralIdentifierPrefix().size() != 0) {
			throw new TODO();
		}
		if (!variablesInScope.contains(tlaGeneralIdentifier.getName().getId()) &&
				!refVariablesInScope.contains(tlaGeneralIdentifier.getName().getId())) {
			ctx.error(new DanglingReferenceIssue(tlaGeneralIdentifier.getUID()));
		}
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws RuntimeException {
		tlaTuple.getElements().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		tlaMaybeAction.getVars().accept(this);
		tlaMaybeAction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		// TODO validate operator name
		tlaOperatorCall.getArgs().forEach(a -> a.accept(this));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		validateBoundsAndBody(tlaQuantifiedExistential.getIds(), tlaQuantifiedExistential.getBody());
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		validateBoundsAndBody(tlaQuantifiedUniversal.getIds(), tlaQuantifiedUniversal.getBody());
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		tlaRecordConstructor.getFields().forEach(f -> f.getValue().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		tlaRecordSet.getFields().forEach(f -> f.getSet().accept(this));
		return null;
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		tlaRequiredAction.getVars().accept(this);
		tlaRequiredAction.getBody().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		tlaSetConstructor.getContents().forEach(e -> e.accept(this));
		return null;
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		validateBoundsAndBody(tlaSetComprehension.getBounds(), tlaSetComprehension.getBody());
		return null;
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		tlaSetRefinement.getFrom().accept(this);
		Set<String> localMacrosInScope = new HashSet<>(macrosInScope);
		Set<String> localProceduresInScope = new HashSet<>(proceduresInScope);
		Set<String> localVariablesInScope = new HashSet<>(variablesInScope);
		Set<String> localRefVariablesInScope = new HashSet<>(refVariablesInScope);
		if (tlaSetRefinement.getIdent().isTuple()) {
			for (TLAIdentifier identifier : tlaSetRefinement.getIdent().getTuple()) {
				String name = identifier.getId();
				localVariablesInScope.add(name);
				localRefVariablesInScope.remove(name);
				localMacrosInScope.remove(name);
				localProceduresInScope.remove(name);
			}
		} else {
			String name = tlaSetRefinement.getIdent().getId().getId();
			localVariablesInScope.add(name);
			localRefVariablesInScope.remove(name);
			localMacrosInScope.remove(name);
			localProceduresInScope.remove(name);
		}
		tlaSetRefinement.getWhen().accept(new ExpressionVariableAccessValidationVisitor(
				ctx, localMacrosInScope, localProceduresInScope, localVariablesInScope, localRefVariablesInScope));
		return null;
	}

	@Override
	public Void visit(TLAString tlaString) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws RuntimeException {
		// TODO validate operation
		tlaUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
		validateIdsAndBody(tlaUniversal.getIds(), tlaUniversal.getBody());
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
