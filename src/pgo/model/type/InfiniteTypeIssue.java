package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class InfiniteTypeIssue extends Issue {
	private final PGoType lhs;
	private final PGoType rhs;

	public InfiniteTypeIssue(PGoType lhs, PGoType rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PGoType getLhs() {
		return lhs;
	}

	public PGoType getRhs() {
		return rhs;
	}
}
