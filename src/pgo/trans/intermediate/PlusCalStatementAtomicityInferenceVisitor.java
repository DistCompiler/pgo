package pgo.trans.intermediate;

import pgo.model.pcal.*;
import pgo.scope.UID;

import java.util.function.Consumer;

public class PlusCalStatementAtomicityInferenceVisitor extends StatementVisitor<Void, RuntimeException> {
	Consumer<UID> captureRead;
	Consumer<UID> captureWrite;
	TLAExpressionAtomicityInferenceVisitor visitor;

	public PlusCalStatementAtomicityInferenceVisitor(Consumer<UID> captureRead, Consumer<UID> captureWrite) {
		this.captureRead = captureRead;
		this.captureWrite = captureWrite;
		this.visitor = new TLAExpressionAtomicityInferenceVisitor(captureRead);
	}

	@Override
	public Void visit(LabeledStatements labeledStatements) throws RuntimeException {
		labeledStatements.getStatements().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(While while1) throws RuntimeException {
		while1.getCondition().accept(visitor);
		while1.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(If if1) throws RuntimeException {
		if1.getCondition().accept(visitor);
		if1.getYes().forEach(s -> s.accept(this));
		if1.getNo().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(Either either) throws RuntimeException {
		either.getCases().forEach(c -> c.forEach(s -> s.accept(this)));
		return null;
	}

	@Override
	public Void visit(Assignment assignment) throws RuntimeException {
		for (AssignmentPair pair : assignment.getPairs()) {
			pair.getLhs().accept(visitor).forEach(this.captureWrite);
			pair.getRhs().accept(visitor);
		}
		return null;
	}

	@Override
	public Void visit(Return return1) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(Skip skip) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(Call call) throws RuntimeException {
		call.getArguments().forEach(a -> a.accept(visitor));
		return null;
	}

	@Override
	public Void visit(MacroCall macroCall) throws RuntimeException {
		throw new RuntimeException("unreachable");
	}

	@Override
	public Void visit(With with) throws RuntimeException {
		with.getVariable().getValue().accept(visitor);
		with.getBody().forEach(s -> s.accept(this));
		return null;
	}

	@Override
	public Void visit(Print print) throws RuntimeException {
		print.getValue().accept(visitor);
		return null;
	}

	@Override
	public Void visit(Assert assert1) throws RuntimeException {
		assert1.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(Await await) throws RuntimeException {
		await.getCondition().accept(visitor);
		return null;
	}

	@Override
	public Void visit(Goto goto1) throws RuntimeException {
		// nothing to do
		return null;
	}
}
