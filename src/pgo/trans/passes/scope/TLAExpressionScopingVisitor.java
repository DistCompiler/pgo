package pgo.trans.passes.scope;

import pgo.InternalCompilerError;
import pgo.TODO;
import pgo.model.tla.*;
import pgo.modules.TLAModuleLoader;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.trans.intermediate.QualifiedName;

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
	public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		tlaFunctionCall.getFunction().accept(this);
		for (TLAExpression param : tlaFunctionCall.getParams()) {
			param.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLABinOp tlaBinOp) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(tlaBinOp.getPrefix(), tlaBinOp.getOperation().getValue()),
				tlaBinOp.getOperation().getUID());
		tlaBinOp.getLHS().accept(this);
		tlaBinOp.getRHS().accept(this);
		return null;
	}

	@Override
	public Void visit(TLABool tlaBool) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLACase tlaCase) throws RuntimeException {
		for (TLACaseArm arm : tlaCase.getArms()) {
			arm.getCondition().accept(this);
			arm.getResult().accept(this);
		}
		if (tlaCase.getOther() != null) {
			tlaCase.getOther().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLADot tlaDot) throws RuntimeException {
		tlaDot.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAIdentifier id : tlaExistential.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		tlaExistential.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws RuntimeException {
		TLAScopeBuilder argScope = builder.makeNestedScope();
		handleQuantifierBounds(argScope, tlaFunction.getArguments());
		tlaFunction.getBody().accept(new TLAExpressionScopingVisitor(argScope, registry, loader, moduleRecursionSet));
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
		for (TLAFunctionSubstitutionPair pair : tlaFunctionSubstitution.getSubstitutions()) {
			pair.getValue().accept(this);
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
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAUnit unit : tlaLet.getDefinitions()) {
			unit.accept(new TLAUnitScopingVisitor(nested.getIssueContext(), nested, null, null, null));
		}
		tlaLet.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		builder.reference(QualifiedName.fromTLAPrefix(tlaGeneralIdentifier.getGeneralIdentifierPrefix(), tlaGeneralIdentifier.getName().getId()), tlaGeneralIdentifier.getUID());
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws RuntimeException {
		for (TLAExpression element : tlaTuple.getElements()) {
			element.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		tlaMaybeAction.getBody().accept(this);
		tlaMaybeAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(tlaOperatorCall.getPrefix(), tlaOperatorCall.getName().getId()),
				tlaOperatorCall.getName().getUID());
		for (TLAExpression arg : tlaOperatorCall.getArgs()) {
			arg.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, tlaQuantifiedExistential.getIds());
		tlaQuantifiedExistential.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, tlaQuantifiedUniversal.getIds());
		tlaQuantifiedUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		for (TLARecordConstructor.Field f : tlaRecordConstructor.getFields()) {
			f.getValue().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		for (TLARecordSet.Field f : tlaRecordSet.getFields()) {
			f.getSet().accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		tlaRequiredAction.getBody().accept(this);
		tlaRequiredAction.getVars().accept(this);
		return null;
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		for (TLAExpression elem : tlaSetConstructor.getContents()) {
			elem.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		handleQuantifierBounds(nested, tlaSetComprehension.getBounds());
		tlaSetComprehension.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		tlaSetRefinement.getFrom().accept(this);
		TLAScopeBuilder nested = builder.makeNestedScope();
		TLAIdentifierOrTuple ident = tlaSetRefinement.getIdent();
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
		tlaSetRefinement.getWhen().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
		return null;
	}

	@Override
	public Void visit(TLAString tlaString) throws RuntimeException {
		// pass
		return null;
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws RuntimeException {
		builder.reference(
				QualifiedName.fromTLAPrefix(tlaUnary.getPrefix(), tlaUnary.getOperation().getValue()),
				tlaUnary.getOperation().getUID());
		tlaUnary.getOperand().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
		TLAScopeBuilder nested = builder.makeNestedScope();
		for (TLAIdentifier id : tlaUniversal.getIds()) {
			nested.defineLocal(id.getId(), id.getUID());
		}
		tlaUniversal.getBody().accept(new TLAExpressionScopingVisitor(nested, registry, loader, moduleRecursionSet));
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
		// TODO make this work for general identifiers
		builder.reference(new QualifiedName(tlaRef.getTarget()), tlaRef.getUID());
		return null;
	}
}
