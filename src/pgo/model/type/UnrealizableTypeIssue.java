package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class UnrealizableTypeIssue extends Issue {
	private PGoType type;

	public UnrealizableTypeIssue(PGoType type) {
		this.type = type;
	}

	public PGoType getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
