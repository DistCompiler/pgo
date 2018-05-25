package pgo.trans.intermediate;

import java.util.Arrays;
import java.util.Map;

import pgo.model.golang.BlockBuilder;
import pgo.model.golang.Builtins;
import pgo.model.golang.Expression;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpressionVisitor;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUniversal;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class TLAExpressionSingleThreadedCodeGenVisitor extends PGoTLAExpressionVisitor<Expression, RuntimeException> {

	private BlockBuilder builder;
	private DefinitionRegistry registry;
	private Map<UID, PGoType> typeMap;

	public TLAExpressionSingleThreadedCodeGenVisitor(BlockBuilder builder, DefinitionRegistry registry, Map<UID, PGoType> typeMap) {
		this.builder = builder;
		this.registry = registry;
		this.typeMap = typeMap;
	}

	@Override
	public Expression visit(PGoTLAFunctionCall pGoTLAFunctionCall) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLABinOp pGoTLABinOp) throws RuntimeException {
		UID ref = registry.followReference(pGoTLABinOp.getOperation().getUID());
		OperatorAccessor op = registry.findOperator(ref);
		return op.generateGo(
				builder, pGoTLABinOp, registry,
				Arrays.asList(
						pGoTLABinOp.getLHS().accept(this),
						pGoTLABinOp.getRHS().accept(this)),
				typeMap);
	}

	@Override
	public Expression visit(PGoTLABool pGoTLABool) throws RuntimeException {
		return pGoTLABool.getValue() ? Builtins.True : Builtins.False;
	}

	@Override
	public Expression visit(PGoTLACase pGoTLACase) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAExistential pGoTLAExistential) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunction pGoTLAFunction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunctionSet pGoTLAFunctionSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAFunctionSubstitution pGoTLAFunctionSubstitution) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAIf pGoTLAIf) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLALet pGoTLALet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAGeneralIdentifier pGoTLAVariable) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLATuple pGoTLATuple) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAMaybeAction pGoTLAMaybeAction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLANumber pGoTLANumber) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAOperatorCall pGoTLAOperatorCall) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAQuantifiedExistential pGoTLAQuantifiedExistential) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAQuantifiedUniversal pGoTLAQuantifiedUniversal) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARecordConstructor pGoTLARecordConstructor) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARecordSet pGoTLARecordSet) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLARequiredAction pGoTLARequiredAction) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLASetConstructor pGoTLASetConstructor) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLASetComprehension pGoTLASetComprehension) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLASetRefinement pGoTLASetRefinement) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAString pGoTLAString) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAUnary pGoTLAUnary) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PGoTLAUniversal pGoTLAUniversal) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

	@Override
	public Expression visit(PlusCalDefaultInitValue plusCalDefaultInitValue) throws RuntimeException {
		throw new RuntimeException("TODO");
	}

}
