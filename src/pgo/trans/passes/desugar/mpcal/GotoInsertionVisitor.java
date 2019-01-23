package pgo.trans.passes.desugar.mpcal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class GotoInsertionVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final PlusCalStatement previousStatement;
	private final PlusCalGoto gotoStatement;

	private GotoInsertionVisitor(PlusCalStatement previousStatement, PlusCalGoto gotoStatement) {
		this.gotoStatement = gotoStatement;
		this.previousStatement = previousStatement;
	}

	static List<PlusCalStatement> insertGoto(PlusCalGoto gotoStmt, List<PlusCalStatement> statements) {
		if (statements.size() == 0) {
			return Collections.singletonList(gotoStmt);
		}
		List<PlusCalStatement> result = new ArrayList<>(statements);
		PlusCalStatement lastStatement = result.remove(result.size() - 1);
		PlusCalStatement nextToLastStatement = result.size() > 0 ? result.remove(result.size() - 1) : null;
		result.addAll(lastStatement.accept(new GotoInsertionVisitor(nextToLastStatement, gotoStmt)));
		return result;
	}

	private List<PlusCalStatement> gotoAtEnd(PlusCalStatement currentStatement) {
		List<PlusCalStatement> result = helper(currentStatement);
		result.add(gotoStatement);
		return result;
	}

	private List<PlusCalStatement> helper(PlusCalStatement toInsert) {
		List<PlusCalStatement> result = new ArrayList<>();
		if (previousStatement != null) {
			result.add(previousStatement);
		}
		result.add(toInsert);
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		if (previousStatement != null) {
			result.add(previousStatement);
		}
		result.add(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(),
				insertGoto(gotoStatement, plusCalLabeledStatements.getStatements())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		if (previousStatement != null) {
			result.add(previousStatement);
		}
		result.add(new PlusCalIf(
				plusCalIf.getLocation(),
				plusCalIf.getCondition(),
				insertGoto(gotoStatement, plusCalIf.getYes()),
				insertGoto(gotoStatement, plusCalIf.getNo())));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		List<PlusCalStatement> result = new ArrayList<>();
		if (previousStatement != null) {
			result.add(previousStatement);
		}
		List<List<PlusCalStatement>> cases = new ArrayList<>();
		for (List<PlusCalStatement> aCase : plusCalEither.getCases()) {
			cases.add(insertGoto(gotoStatement, aCase));
		}
		result.add(new PlusCalEither(plusCalEither.getLocation(), cases));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		return gotoAtEnd(plusCalAssignment);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// the user wants to return instead. Let that happen.
		return helper(plusCalReturn);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// remove the skip statement
		return helper(gotoStatement);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		return gotoAtEnd(plusCalCall);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		return gotoAtEnd(plusCalWith);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return gotoAtEnd(plusCalPrint);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return gotoAtEnd(plusCalAssert);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return gotoAtEnd(plusCalAwait);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// the user want to goto somewhere else. Let that happen.
		return helper(plusCalGoto);
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
