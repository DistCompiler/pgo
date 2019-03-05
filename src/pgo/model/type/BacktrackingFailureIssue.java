package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.type.constraint.PolymorphicConstraint;

public class BacktrackingFailureIssue extends Issue {
	private PolymorphicConstraint polymorphicConstraint;

	public BacktrackingFailureIssue(PolymorphicConstraint polymorphicConstraint) {
		this.polymorphicConstraint = polymorphicConstraint;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PolymorphicConstraint getPolymorphicConstraint() {
		return polymorphicConstraint;
	}
}
