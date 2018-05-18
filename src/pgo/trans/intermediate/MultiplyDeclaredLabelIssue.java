package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.scope.UID;

public class MultiplyDeclaredLabelIssue extends Issue {

	private UID first;
	private UID second;

	public MultiplyDeclaredLabelIssue(UID first, UID second) {
		this.first = first;
		this.second = second;
	}

	public UID getFirst() {
		return first;
	}

	public UID getSecond() {
		return second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
