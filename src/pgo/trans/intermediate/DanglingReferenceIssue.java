package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.scope.UID;

public class DanglingReferenceIssue extends Issue {
	
	UID from;

	public DanglingReferenceIssue(UID from) {
		super();
		this.from = from;
	}

	public UID getFrom() {
		return from;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toString() {
		return "Dangling reference for " + from.toString();
	}
}
