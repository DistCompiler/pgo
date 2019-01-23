package pgo.trans.passes.codegen.pluscal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.ArrayList;
import java.util.List;

public class WriteBackInsertionVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final PlusCalStatement previousStatement;
	private final List<PlusCalStatement> writeBacks;

	WriteBackInsertionVisitor(PlusCalStatement previousStatement, List<PlusCalStatement> writeBacks) {
		this.previousStatement = previousStatement;
		this.writeBacks = writeBacks;
	}

	static List<PlusCalStatement> insertWriteBacks(List<PlusCalStatement> statements,
	                                               List<PlusCalStatement> writeBacks) {
		if (statements.size() == 0) {
			return writeBacks;
		}
		List<PlusCalStatement> result = new ArrayList<>(statements);
		PlusCalStatement lastStatement = result.remove(result.size() - 1);
		PlusCalStatement nextToLastStatement = result.size() > 0 ? result.remove(result.size() - 1) : null;
		result.addAll(lastStatement.accept(new WriteBackInsertionVisitor(nextToLastStatement, writeBacks)));
		return result;
	}

	private List<PlusCalStatement> helper() {
		List<PlusCalStatement> result = new ArrayList<>();
		if (previousStatement != null) {
			result.add(previousStatement);
		}
		return result;
	}

	private List<PlusCalStatement> writeBacksAtEnd(PlusCalStatement plusCalStatement) {
		List<PlusCalStatement> result = helper();
		result.add(plusCalStatement);
		result.addAll(writeBacks);
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		List<PlusCalStatement> result = helper();
		result.add(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(),
				plusCalLabeledStatements.getLabel(),
				insertWriteBacks(plusCalLabeledStatements.getStatements(), writeBacks)));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		List<PlusCalStatement> result = helper();
		result.add(new PlusCalIf(
				plusCalIf.getLocation(),
				plusCalIf.getCondition(),
				insertWriteBacks(plusCalIf.getYes(), writeBacks),
				insertWriteBacks(plusCalIf.getNo(), writeBacks)));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		List<PlusCalStatement> result = helper();
		List<List<PlusCalStatement>> cases = new ArrayList<>();
		for (List<PlusCalStatement> aCase : plusCalEither.getCases()) {
			cases.add(insertWriteBacks(aCase, writeBacks));
		}
		result.add(new PlusCalEither(plusCalEither.getLocation(), cases));
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		return writeBacksAtEnd(plusCalAssignment);
	}

	private List<PlusCalStatement> handleReturnAndGoto(PlusCalStatement plusCalStatement) {
		if (previousStatement instanceof PlusCalCall) {
			List<PlusCalStatement> result = new ArrayList<>(writeBacks);
			result.add(previousStatement);
			result.add(plusCalStatement);
			return result;
		}
		List<PlusCalStatement> result = helper();
		result.addAll(writeBacks);
		result.add(plusCalStatement);
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		return handleReturnAndGoto(plusCalReturn);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
		// remove skip
		List<PlusCalStatement> result = helper();
		result.addAll(writeBacks);
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		List<PlusCalStatement> result = helper();
		result.addAll(writeBacks);
		result.add(plusCalCall);
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
		return writeBacksAtEnd(plusCalWith);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
		return writeBacksAtEnd(plusCalPrint);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
		return writeBacksAtEnd(plusCalAssert);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
		return writeBacksAtEnd(plusCalAwait);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		return handleReturnAndGoto(plusCalGoto);
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}

