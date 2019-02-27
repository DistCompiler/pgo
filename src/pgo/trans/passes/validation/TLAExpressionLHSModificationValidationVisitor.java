package pgo.trans.passes.validation;

import pgo.Unreachable;
import pgo.errors.IssueContext;
import pgo.model.tla.*;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;

import java.util.Set;

public class TLAExpressionLHSModificationValidationVisitor extends TLAExpressionVisitor<Void, RuntimeException> {
	private final IssueContext ctx;
	private final DefinitionRegistry registry;
	private final Set<UID> nonRefParams;

	public TLAExpressionLHSModificationValidationVisitor(IssueContext ctx, DefinitionRegistry registry,
	                                                     Set<UID> nonRefParams) {
		this.ctx = ctx;
		this.registry = registry;
		this.nonRefParams = nonRefParams;
	}

	@Override
	public Void visit(TLAFunctionCall tlaFunctionCall) throws RuntimeException {
		// no need to check params because they are only read
		tlaFunctionCall.getFunction().accept(this);
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
		throw new Unreachable();
	}

	@Override
	public Void visit(TLACase tlaCase) throws RuntimeException {
		for (TLACaseArm arm : tlaCase.getArms()) {
			// no need to check condition because they are only read
			arm.getResult().accept(this);
		}
		tlaCase.getOther().accept(this);
		return null;
	}

	@Override
	public Void visit(TLADot tlaDot) throws RuntimeException {
		tlaDot.getExpression().accept(this);
		return null;
	}

	@Override
	public Void visit(TLAExistential tlaExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFairness tlaFairness) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunction tlaFunction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSet tlaFunctionSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAFunctionSubstitution tlaFunctionSubstitution) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAIf tlaIf) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLALet tlaLet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAGeneralIdentifier tlaGeneralIdentifier) throws RuntimeException {
		UID varUID = registry.followReference(tlaGeneralIdentifier.getUID());
		if (nonRefParams.contains(varUID)) {
			ctx.error(new NonRefParamModification(varUID));
		}
		return null;
	}

	@Override
	public Void visit(TLATuple tlaTuple) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAMaybeAction tlaMaybeAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLANumber tlaNumber) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAOperatorCall tlaOperatorCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedExistential tlaQuantifiedExistential) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAQuantifiedUniversal tlaQuantifiedUniversal) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordConstructor tlaRecordConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARecordSet tlaRecordSet) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARef tlaRef) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLARequiredAction tlaRequiredAction) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetConstructor tlaSetConstructor) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetComprehension tlaSetComprehension) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASetRefinement tlaSetRefinement) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASpecialVariableVariable tlaSpecialVariableVariable) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLASpecialVariableValue tlaSpecialVariableValue) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAString tlaString) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUnary tlaUnary) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(TLAUniversal tlaUniversal) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Void visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		throw new Unreachable();
	}
}
