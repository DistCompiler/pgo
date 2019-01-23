package pgo.trans.passes.desugar.mpcal;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

class ModularPlusCalDesugarVisitor extends PlusCalStatementVisitor<List<PlusCalStatement>, RuntimeException> {
	private List<PlusCalStatement> desugarStatements(List<PlusCalStatement> statements) {
		List<PlusCalStatement> result = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			result.addAll(statement.accept(this));
		}
		return result;
	}

	private PlusCalLabeledStatements desugarWhile(SourceLocation location, PlusCalLabel label,
	                                              PlusCalWhile plusCalWhile, List<PlusCalStatement> rest) {
		// a while loop is desugared into and if and a goto due to the possibility that the condition of the while loop
		// might contain a mapped variable read
		//
		// lb: while (f(a)) {
		//       stmt...
		//     };
		//     stmt...
		//
		// is translated into
		//
		// lb: if (f(a)) {
		//       stmt...
		//       goto lb;
		//     } else {
		//       stmt...
		//     };
		//
		// so that further codegen can possibly translate that into
		//
		// lb: aRead := a
		//     if (f(aRead)) {
		//       stmt...
		//       goto lb;
		//     } else {
		//       stmt...
		//     };
		//
		// (in this case, a is macro mapped)
		List<PlusCalStatement> body = desugarStatements(plusCalWhile.getBody());
		PlusCalGoto gotoStmt = new PlusCalGoto(plusCalWhile.getLocation(), label.getName());
		if (body.size() == 0) {
			body.add(gotoStmt);
		} else {
			GotoInsertionVisitor.insertGoto(gotoStmt, body);
		}
		return new PlusCalLabeledStatements(
				location,
				label,
				Collections.singletonList(new PlusCalIf(
						plusCalWhile.getLocation(),
						plusCalWhile.getCondition(),
						body,
						desugarStatements(rest))));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalLabeledStatements plusCalLabeledStatements) throws RuntimeException {
		// look ahead to handle while statements
		SourceLocation location = plusCalLabeledStatements.getLocation();
		PlusCalLabel label = plusCalLabeledStatements.getLabel();
		List<PlusCalStatement> statements = plusCalLabeledStatements.getStatements();
		if (plusCalLabeledStatements.getStatements().get(0) instanceof PlusCalWhile) {
			PlusCalWhile plusCalWhile = (PlusCalWhile) plusCalLabeledStatements.getStatements().get(0);
			List<PlusCalStatement> rest = plusCalLabeledStatements.getStatements().subList(1, statements.size());
			return Collections.singletonList(desugarWhile(location, label, plusCalWhile, rest));
		}
		List<PlusCalStatement> transformedStatements = new ArrayList<>();
		for (PlusCalStatement statement : statements) {
			transformedStatements.addAll(statement.accept(new ModularPlusCalDesugarVisitor()));
		}
		return Collections.singletonList(new PlusCalLabeledStatements(
				location, plusCalLabeledStatements.getLabel(), transformedStatements));
	}

	@Override
	public List<PlusCalStatement> visit(PlusCalWhile plusCalWhile) throws RuntimeException {
		throw new Unreachable();
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
