package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAExpressionVisitor;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.parser.Located;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ModularPlusCalMappingMacroExpansionVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	protected final TemporaryBinding temporaryBinding;
	protected final TLAExpression variable;
	protected final TLAExpressionVisitor<TLAExpression, RuntimeException> visitor;

	public ModularPlusCalMappingMacroExpansionVisitor(TemporaryBinding temporaryBinding, TLAExpression variable,
	                                                  TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		this.temporaryBinding = temporaryBinding;
		this.variable = variable;
		this.visitor = visitor;
	}

	private List<PlusCalStatement> substituteStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		return Collections.singletonList(new PlusCalWhile(
				plusCalWhile.getLocation(),
				plusCalWhile.getCondition().accept(visitor),
				substituteStatements(plusCalWhile.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		return Collections.singletonList(new PlusCalIf(
				plusCalIf.getLocation(),
				plusCalIf.getCondition().accept(visitor),
				substituteStatements(plusCalIf.getYes()),
				substituteStatements(plusCalIf.getNo())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		List<List<PlusCalStatement>> cases = new ArrayList<>();
		for (List<PlusCalStatement> aCase : plusCalEither.getCases()) {
			cases.add(substituteStatements(aCase));
		}
		return Collections.singletonList(new PlusCalEither(plusCalEither.getLocation(), cases));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		List<PlusCalAssignmentPair> pairs = new ArrayList<>();
		for (PlusCalAssignmentPair pair : plusCalAssignment.getPairs()) {
			pairs.add(new PlusCalAssignmentPair(
					pair.getLocation(),
					pair.getLhs().accept(visitor),
					pair.getRhs().accept(visitor)));
		}
		return Collections.singletonList(new PlusCalAssignment(plusCalAssignment.getLocation(), pairs));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return Collections.singletonList(new PlusCalReturn(plusCalReturn.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		return Collections.singletonList(new PlusCalSkip(plusCalSkip.getLocation()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<TLAExpression> params = new ArrayList<>();
		for (TLAExpression argument : plusCalCall.getArguments()) {
			params.add(argument.accept(visitor));
		}
		return Collections.singletonList(new PlusCalCall(
				plusCalCall.getLocation(),
				plusCalCall.getTarget(),
				params));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		List<PlusCalVariableDeclaration> declarations = new ArrayList<>();
		for (PlusCalVariableDeclaration declaration : plusCalWith.getVariables()) {
			TLAGeneralIdentifier fresh = temporaryBinding.freshVariable(
					declaration.getLocation(), declaration.getUID(), declaration.getName().getValue());
			declarations.add(new PlusCalVariableDeclaration(
					declaration.getLocation(),
					new Located<>(declaration.getName().getLocation(), fresh.getName().getId()),
					false,
					declaration.isSet(),
					declaration.getValue().accept(visitor)));
		}
		return Collections.singletonList(new PlusCalWith(
				plusCalWith.getLocation(),
				declarations,
				substituteStatements(plusCalWith.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return Collections.singletonList(new PlusCalPrint(
				plusCalPrint.getLocation(),
				plusCalPrint.getValue().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssert(
				plusCalAssert.getLocation(),
				plusCalAssert.getCondition().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return Collections.singletonList(new PlusCalAwait(
				plusCalAwait.getLocation(),
				plusCalAwait.getCondition().accept(visitor)));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return Collections.singletonList(new PlusCalGoto(plusCalGoto.getLocation(), plusCalGoto.getTarget()));
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return Collections.singletonList(new PlusCalAssignment(
				modularPlusCalYield.getLocation(),
				Collections.singletonList(new PlusCalAssignmentPair(
						modularPlusCalYield.getLocation(),
						variable,
						modularPlusCalYield.getExpression().accept(visitor)))));
	}
}
