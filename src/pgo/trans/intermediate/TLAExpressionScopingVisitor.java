package pgo.trans.intermediate;

import pgo.InternalCompilerError;
import pgo.model.tla.*;
import pgo.modules.TLAModuleLoader;
import pgo.scope.UID;

import java.util.List;
import java.util.Set;

public class TLAExpressionScopingVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	protected final TLAScopeBuilder builder;
	protected final DefinitionRegistry registry;
	private final TLAModuleLoader loader;
	private final Set<String> moduleRecursionSet;

	public TLAExpressionScopingVisitor(TLAScopeBuilder builder, DefinitionRegistry registry, TLAModuleLoader loader,
	                                   Set<String> moduleRecursionSet) {
		this.builder = builder;
		this.registry = registry;
		this.loader = loader;
		this.moduleRecursionSet = moduleRecursionSet;
	}

	private void handleQuantifierBounds(TLAScopeBuilder scope, List<TLAQuantifierBound> bounds) {
		for (TLAQuantifierBound qb : bounds) {
			for (TLAIdentifier id : qb.getIds()) {
				scope.defineLocal(id.getId(), id.getUID());
				registry.addLocalVariable(id.getUID());
			}
			qb.getSet().accept(this);
		}
	}

	@Override
	public Void visit(TLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		pGoTLAFunctionCall.getFunction().accept(this);
		for (TLAExpression param : pGoTLAFunctionCall.getParams()) {
			param.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLABinOp TLABinOp) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(TLABinOp.getPrefix(), TLABinOp.getOperation().getValue()),
				TLABinOp.getOperation().getUID());
		TLABinOp.getLHS().accept(this);
		TLABinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(TLABool TLABool) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLACase TLACase) throws RuntimeException {
		for (TLACaseArm arm : TLACase.getArms()) {
			arm.getCondition().accept(this);
			arm.getResult().accept(this);
		}
		if (TLACase.getOther() != null) {
			TLACase.getOther().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAExistential TLAExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAIdentifier id : TLAExistential.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		TLAExistential.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAFunction pGoTLAFunction) throws RuntimeException {
		TLAScopeBuilder argScope = builder.makeNestedScope();
		handleQuantifierBounds(argScope, pGoTLAFunction.getArguments());
		pGoTLAFunction.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
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
		for (TLAFunctionSubstitutionPair pair : pGoTLAFunctionSubstitution.getSubstitutions()) {
			pair.getValue().accept(this);
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
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAUnit unit : pGoTLALet.getDefinitions()) {
			unit.accept(new TLAUnitScopingVisitor(nested.getIssueContext(), nested, null, null, null));
		}
		pGoTLALet.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		builder.reference(QualifiedName.fromTLAPrefix(pGoTLAVariable.getGeneralIdentifierPrefix(), pGoTLAVariable.getName().getId()), pGoTLAVariable.getUID());
		return null;
	}

	@Override
	public Void visit(TLATuple pGoTLATuple) throws RuntimeException {
		for (TLAExpression element : pGoTLATuple.getElements()) {
			element.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		pGoTLAMaybeAction.getBody().accept(this);
		pGoTLAMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber pGoTLANumber) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(pGoTLAOperatorCall.getPrefix(), pGoTLAOperatorCall.getName().getId()),
				pGoTLAOperatorCall.getName().getUID());
		for (TLAExpression arg : pGoTLAOperatorCall.getArgs()) {
			arg.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, pGoTLAQuantifiedExistential.getIds());
		pGoTLAQuantifiedExistential.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, pGoTLAQuantifiedUniversal.getIds());
		pGoTLAQuantifiedUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		for (TLARecordConstructor.Field f : pGoTLARecordConstructor.getFields()) {
			f.getValue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLARecordSet pGoTLARecordSet) throws RuntimeException {
		for (TLARecordSet.Field f : pGoTLARecordSet.getFields()) {
			f.getSet().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		pGoTLARequiredAction.getBody().accept(this);
		pGoTLARequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		for (TLAExpression elem : pGoTLASetConstructor.getContents()) {
			elem.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, pGoTLASetComprehension.getBounds());
		pGoTLASetComprehension.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		pGoTLASetRefinement.getFrom().accept(this);
		TLAScopeBuilder nested = builder.makeNestedScope();
		TLAIdentifierOrTuple ident = pGoTLASetRefinement.getIdent();
		if (ident.isTuple()) {
			for (TLAIdentifier id : ident.getTuple()) {
				nested.defineLocal(id.getId(), id.getUID());
				// TODO: BAD BAD, make pattern matching over tuples work
			}
		} else {
			UID uid = ident.getId().getUID();
			nested.defineLocal(ident.getId().getId(), uid);
			registry.addLocalVariable(uid);
		}
		pGoTLASetRefinement.getWhen().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAString pGoTLAString) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLAUnary pGoTLAUnary) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(pGoTLAUnary.getPrefix(), pGoTLAUnary.getOperation().getValue()),
				pGoTLAUnary.getOperation().getUID());
		pGoTLAUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal pGoTLAUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAIdentifier id : pGoTLAUniversal.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		pGoTLAUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		// has no effect on scoping
		return null;
	}

	@Override
	public Void visit(TLAFairness fairness) throws RuntimeException {
		fairness.getVars().accept(this);
		fairness.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new InternalCompilerError();
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		throw new InternalCompilerError();
	}
}
