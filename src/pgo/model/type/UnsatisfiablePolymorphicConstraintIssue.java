package pgo.model.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.util.Origin;

import java.util.List;

public class UnsatisfiablePolymorphicConstraintIssue extends Issue {

	private Origin origin;
	private List<PGoType> argTypes;

	public UnsatisfiablePolymorphicConstraintIssue(Origin origin, List<PGoType> argTypes) {
		this.origin = origin;
		this.argTypes = argTypes;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Origin getOrigin() {
		return origin;
	}

	public List<PGoType> getArgTypes() {
		return argTypes;
	}
}
