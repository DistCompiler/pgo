package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class InfiniteTypeIssue extends Issue {
	private final Type lhs;
	private final Type rhs;

	public InfiniteTypeIssue(Type lhs, Type rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Type getLhs() {
		return lhs;
	}

	public Type getRhs() {
		return rhs;
	}
}
