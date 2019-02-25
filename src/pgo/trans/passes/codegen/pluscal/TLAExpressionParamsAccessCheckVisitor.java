package pgo.trans.passes.codegen.pluscal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Map;

public class TLAExpressionParamsAccessCheckVisitor extends TLAExpressionVisitor<Boolean, RuntimeException> {
	private final DefinitionRegistry registry;
	private final Map<UID, PlusCalVariableDeclaration> params;
	private final Map<UID, PlusCalVariableDeclaration> variables;

	public TLAExpressionParamsAccessCheckVisitor(DefinitionRegistry registry,
	                                             Map<UID, PlusCalVariableDeclaration> params,
	                                             Map<UID, PlusCalVariableDeclaration> variables) {
		this.registry = registry;
		this.params = params;
		this.variables = variables;
	}

	@Override
	public Boolean visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		return tlaFunctionCall.getFunction().accept(this) ||
				tlaFunctionCall.getParams().stream().anyMatch(a -> a.accept(this));
	}

	@Override
	public Boolean visit(TLABinOp tlaBinOp) throws RuntimeException {
		return tlaBinOp.getLHS().accept(this) || tlaBinOp.getRHS().accept(this);
	}

	@Override
	public Boolean visit(TLABool tlaBool) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(TLACase tlaCase) throws RuntimeException {
		return tlaCase.getArms()
				.stream()
				.anyMatch(a -> a.getCondition().accept(this) || a.getResult().accept(this)) ||
				(tlaCase.getOther() != null && tlaCase.getOther().accept(this));
	}

	@Override
	public Boolean visit(TLADot tlaDot) throws RuntimeException {
		return tlaDot.getExpression().accept(this);
	}

	@Override
	public Boolean visit(TLAExistential tlaExistential) throws RuntimeException {
		return tlaExistential.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAFunction tlaFunction) throws RuntimeException {
		return tlaFunction.getArguments().stream().anyMatch(p -> p.getSet().accept(this)) ||
				tlaFunction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		return tlaFunctionSet.getFrom().accept(this) || tlaFunctionSet.getTo().accept(this);
	}

	@Override
	public Boolean visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		return tlaFunctionSubstitution.getSource().accept(this) ||
				tlaFunctionSubstitution.getSubstitutions().stream().anyMatch(p ->
						p.getValue().accept(this) ||
								p.getKeys().stream().anyMatch(k ->
										k.getIndices()
												.stream().anyMatch(i -> i.accept(this))));
	}

	@Override
	public Boolean visit(TLAIf tlaIf) throws RuntimeException {
		return tlaIf.getCond().accept(this) || tlaIf.getTval().accept(this) || tlaIf.getFval().accept(this);
	}

	@Override
	public Boolean visit(TLALet tlaLet) throws RuntimeException {
        throw new TODO();
	}

	@Override
	public Boolean visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (params.containsKey(varUID)) {
			return true;
		}
		if (variables.containsKey(varUID)) {
			return variables.get(varUID).getValue().accept(this);
		}
		return false;
	}

	@Override
	public Boolean visit(TLATuple tlaTuple) throws RuntimeException {
		return tlaTuple.getElements().stream().anyMatch(e -> e.accept(this));
	}

	@Override
	public Boolean visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		return tlaMaybeAction.getVars().accept(this) || tlaMaybeAction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLANumber tlaNumber) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		return tlaOperatorCall.getArgs().stream().anyMatch(a -> a.accept(this));
	}

	@Override
	public Boolean visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		return tlaQuantifiedExistential.getIds().stream().anyMatch(b -> b.getSet().accept(this)) ||
				tlaQuantifiedExistential.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		return tlaQuantifiedUniversal.getIds().stream().anyMatch(b -> b.getSet().accept(this)) ||
				tlaQuantifiedUniversal.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		return tlaRecordConstructor.getFields().stream().anyMatch(f -> f.getValue().accept(this));
	}

	@Override
	public Boolean visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		return tlaRecordSet.getFields().stream().anyMatch(f -> f.getSet().accept(this));
	}

	@Override
	public Boolean visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		return tlaRequiredAction.getVars().accept(this) || tlaRequiredAction.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		return tlaSetConstructor.getContents().stream().anyMatch(c -> c.accept(this));
	}

	@Override
	public Boolean visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		return tlaSetComprehension.getBounds().stream().anyMatch(b -> b.getSet().accept(this)) ||
				tlaSetComprehension.getBody().accept(this);
	}

	@Override
	public Boolean visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		return tlaSetRefinement.getWhen().accept(this) || tlaSetRefinement.getFrom().accept(this);
	}

	@Override
	public Boolean visit(TLAString tlaString) throws RuntimeException {
		return false;
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
		return false;
	}

	@Override
	public Boolean visit(TLAFairness tlaFairness) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
        throw new Unreachable();
	}

	@Override
	public Boolean visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Boolean visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}
}
