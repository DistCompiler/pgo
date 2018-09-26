package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalMacro;

public class MacroNameConflictIssue extends Issue {
	private final PlusCalMacro first;
	private final PlusCalMacro second;

	public MacroNameConflictIssue(PlusCalMacro first, PlusCalMacro second) {
		this.first = first;
		this.second = second;
	}

	public PlusCalMacro getFirst() {
		return first;
	}

	public PlusCalMacro getSecond() {
		return second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
