package pgo.trans.passes.scope;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.util.Origin;

public class ArchetypeNotFoundIssue extends Issue {
	private final Origin origin;
	private final String archetypeName;

	public ArchetypeNotFoundIssue(Origin origin, String archetypeName) {
		this.origin = origin;
		this.archetypeName = archetypeName;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Origin getOrigin() {
		return origin;
	}

	public String getArchetypeName() {
		return archetypeName;
	}
}
