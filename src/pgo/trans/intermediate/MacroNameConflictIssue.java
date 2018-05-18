package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.Macro;

public class MacroNameConflictIssue extends Issue {

	private Macro first;
	private Macro second;

	public MacroNameConflictIssue(Macro first, Macro second) {
		this.first = first;
		this.second = second;
	}

	public Macro getFirst() {
		return first;
	}

	public Macro getSecond() {
		return second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
