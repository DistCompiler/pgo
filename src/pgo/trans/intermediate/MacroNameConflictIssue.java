package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalMacro;

public class MacroNameConflictIssue extends Issue {

	private PlusCalMacro first;
	private PlusCalMacro second;

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
