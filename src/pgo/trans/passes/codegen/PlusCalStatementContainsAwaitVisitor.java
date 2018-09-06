package pgo.trans.passes.codegen;

import pgo.Unreachable;
import pgo.model.mpcal.ModularPlusCalYield;
import pgo.model.pcal.*;

public class PlusCalStatementContainsAwaitVisitor extends PlusCalStatementVisitor<Boolean, RuntimeException> {
	private boolean foundLabeledStatements;

	public PlusCalStatementContainsAwaitVisitor() {
		this(false);
	}

	public PlusCalStatementContainsAwaitVisitor(boolean foundLabeledStatements) {
		this.foundLabeledStatements = foundLabeledStatements;
	}

	@Override
	public Boolean visit(PlusCalLabeledStatements labeledStatements) throws RuntimeException {
		if (foundLabeledStatements) {
			return false;
		}
		foundLabeledStatements = true;
		return labeledStatements.getStatements().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(PlusCalWhile while1) throws RuntimeException {
		return while1.getBody().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(PlusCalIf if1) throws RuntimeException {
		return if1.getYes().stream().anyMatch(s -> s.accept(this)) ||
				if1.getNo().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(PlusCalEither either) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalAssignment assignment) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalReturn return1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalSkip skip) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalCall call) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalMacroCall macroCall) throws RuntimeException {
		throw new Unreachable();
	}

	@Override
	public Boolean visit(PlusCalWith with) throws RuntimeException {
		return with.getBody().stream().anyMatch(s -> s.accept(this));
	}

	@Override
	public Boolean visit(PlusCalPrint print) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalAssert assert1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(PlusCalAwait await) throws RuntimeException {
		return true;
	}

	@Override
	public Boolean visit(PlusCalGoto goto1) throws RuntimeException {
		return false;
	}

	@Override
	public Boolean visit(ModularPlusCalYield modularPlusCalYield) throws RuntimeException {
		return false;
	}
}
