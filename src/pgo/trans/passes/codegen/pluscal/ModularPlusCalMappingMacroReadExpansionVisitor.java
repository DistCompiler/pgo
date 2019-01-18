package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAExpressionVisitor;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLASpecialVariableVariable;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ModularPlusCalMappingMacroReadExpansionVisitor
		extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final TemporaryBinding readTemporaryBinding;
	protected final TemporaryBinding writeTemporaryBinding;
	private final TLAExpression variable;
	protected final UID varUID;
	protected final String nameHint;
	protected final TLAExpressionVisitor<TLAExpression, RuntimeException> visitor;

	public ModularPlusCalMappingMacroReadExpansionVisitor(TemporaryBinding readTemporaryBinding,
	                                                      TemporaryBinding writeTemporaryBinding, TLAExpression variable,
	                                                      UID varUID, String nameHint,
	                                                      TLAExpressionVisitor<TLAExpression, RuntimeException> visitor) {
		this.readTemporaryBinding = readTemporaryBinding;
		this.writeTemporaryBinding = writeTemporaryBinding;
		this.varUID = varUID;
		this.nameHint = nameHint;
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
		List<PlusCalStatement> result = new ArrayList<>();
		List<PlusCalAssignmentPair> pairs = plusCalAssignment.getPairs();
		List<TLAExpression> rhsList = new ArrayList<>();
		if (pairs.size() > 1) {
			for (PlusCalAssignmentPair pair : pairs) {
				SourceLocation location = pair.getLocation();
				TLAExpression rhs = pair.getRhs().accept(visitor);
				TLAGeneralIdentifier rhsRead = readTemporaryBinding.declare(location, new UID(), "rhsRead");
				result.add(new PlusCalAssignment(
						location,
						Collections.singletonList(new PlusCalAssignmentPair(
								location, rhsRead, rhs))));
				rhsList.add(rhsRead);
			}
		} else {
			rhsList.add(pairs.get(0).getRhs().accept(visitor));
		}
		List<PlusCalAssignmentPair> transformedPairs = new ArrayList<>();
		for (int i = 0; i < pairs.size(); i++) {
			PlusCalAssignmentPair pair = pairs.get(i);
			TLAExpression lhs = pair.getLhs();
			TLAExpression rhs = rhsList.get(i);
			if (lhs instanceof TLASpecialVariableVariable) {
				lhs = writeTemporaryBinding.declare(lhs.getLocation(), varUID, nameHint);
			} else {
				lhs = lhs.accept(visitor);
			}
			transformedPairs.add(new PlusCalAssignmentPair(pair.getLocation(), lhs, rhs));
		}
		result.add(new PlusCalAssignment(plusCalAssignment.getLocation(), transformedPairs));
		return result;
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
			TLAGeneralIdentifier fresh = readTemporaryBinding.freshVariable(
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
