package pgo.trans.passes.desugar.mpcal;

import pgo.TODO;
import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class ModularPlusCalDesugarVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private final PlusCalLabel currentLabel;

	ModularPlusCalDesugarVisitor(PlusCalLabel currentLabel) {
		this.currentLabel = currentLabel;
	}

	private List<PlusCalStatement> desugarStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		List<PlusCalStatement> statements = new ArrayList<>();
		for (PlusCalStatement statement : plusCalLabeledStatements.getStatements()) {
			statements.addAll(statement.accept(new ModularPlusCalDesugarVisitor(plusCalLabeledStatements.getLabel())));
		}
		return Collections.singletonList(new PlusCalLabeledStatements(
				plusCalLabeledStatements.getLocation(), plusCalLabeledStatements.getLabel(), statements));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		// a while loop is desugared into and if and a goto due to the possibility that the condition of the while loop
		// might contain a mapped variable read
		//
		// lb: while (f(a)) {
		//       stmt...
		//     }
		//
		// is translated into
		//
		// lb: if (f(a)) {
		//       stmt...
		//       goto lb;
		//     }
		//
		// so that further codegen can possibly translate that into
		//
		// lb: aRead := a
		//     if (f(aRead)) {
		//       stmt...
		//       goto lb;
		//     }
		//
		// (in this case, a is macro mapped)
		List<PlusCalStatement> body = desugarStatements(plusCalWhile.getBody());
		body.add(new PlusCalGoto(plusCalWhile.getLocation(), currentLabel.getName()));
        return Collections.singletonList(new PlusCalIf(
        		plusCalWhile.getLocation(),
		        plusCalWhile.getCondition(),
		        body,
		        Collections.emptyList()));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalIf plusCalIf) throws RuntimeException {
		return Collections.singletonList(new PlusCalIf(
				plusCalIf.getLocation(),
				plusCalIf.getCondition(),
				desugarStatements(plusCalIf.getYes()),
				desugarStatements(plusCalIf.getNo())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalEither plusCalEither) throws RuntimeException {
		List<List<PlusCalStatement>> cases = new ArrayList<>();
		for (List<PlusCalStatement> aCase : plusCalEither.getCases()) {
			cases.add(desugarStatements(aCase));
		}
		return Collections.singletonList(new PlusCalEither(plusCalEither.getLocation(), cases));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssignment plusCalAssignment) throws RuntimeException {
		// nothing to do
		return Collections.singletonList(plusCalAssignment);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalReturn plusCalReturn) throws RuntimeException {
		// nothing to do
		return Collections.singletonList(plusCalReturn);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalSkip plusCalSkip) throws RuntimeException {
        // nothing to do
		return Collections.singletonList(plusCalSkip);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalCall plusCalCall) throws RuntimeException {
		// nothing to do
        return Collections.singletonList(plusCalCall);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWith plusCalWith) throws RuntimeException {
        return Collections.singletonList(new PlusCalWith(
        		plusCalWith.getLocation(),plusCalWith.getVariables(), desugarStatements(plusCalWith.getBody())));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalPrint plusCalPrint) throws RuntimeException {
        // nothing to do
		return Collections.singletonList(plusCalPrint);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAssert plusCalAssert) throws RuntimeException {
        // nothing to do
		return Collections.singletonList(plusCalAssert);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalAwait plusCalAwait) throws RuntimeException {
        // nothing to do
		return Collections.singletonList(plusCalAwait);
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalGoto plusCalGoto) throws RuntimeException {
		// nothing to do
        return Collections.singletonList(plusCalGoto);
	}

	@Override
	public List<PlusCalStatement> visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		throw new Unreachable();
	}
}
