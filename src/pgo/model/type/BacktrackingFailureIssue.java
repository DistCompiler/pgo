package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class BacktrackingFailureIssue extends Issue {
	private PGoTypePolymorphicConstraint polymorphicConstraint;

	public BacktrackingFailureIssue(PGoTypePolymorphicConstraint polymorphicConstraint) {
		this.polymorphicConstraint = polymorphicConstraint;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PGoTypePolymorphicConstraint getPolymorphicConstraint() {
		return polymorphicConstraint;
	}
}
