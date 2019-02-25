package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class UnsatisfiableConstraintIssue extends Issue {
	private PGoType lhs;
	private PGoType rhs;

	public UnsatisfiableConstraintIssue(PGoType lhs, PGoType rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public PGoType getLhs() {
		return lhs;
	}

	public PGoType getRhs() {
		return rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
