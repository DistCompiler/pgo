package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class UnsatisfiableConstraintIssue extends Issue {
	private final Type lhs;
	private final Type rhs;

	public UnsatisfiableConstraintIssue(Type lhs, Type rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public Type getLhs() {
		return lhs;
	}

	public Type getRhs() {
		return rhs;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
