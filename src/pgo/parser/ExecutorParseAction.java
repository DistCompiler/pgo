package pgo.parser;

import pgo.InternalCompilerError;

import java.util.List;
import java.util.function.Supplier;

public class ExecutorParseAction extends ParseAction {

	private Supplier<List<ParseAction>> toExecute;

	public ExecutorParseAction(Supplier<List<ParseAction>> toExecute) {
		this.toExecute = toExecute;
	}

	public Supplier<List<ParseAction>> getToExecute() { return toExecute; }

	@Override
	public String toString() {
		return "EXE "+toExecute;
	}

	@Override
	public boolean isDecidable() {
		return false;
	}

	@Override
	public boolean mergeCompatible(ParseAction other) {
		return false;
	}

	@Override
	protected void mergeImpl(ParseAction other) {
		throw new InternalCompilerError();
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
