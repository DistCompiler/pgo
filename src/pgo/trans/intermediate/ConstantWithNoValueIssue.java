package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.scope.UID;

public class ConstantWithNoValueIssue extends Issue {

	private String name;
	private UID definition;

	public ConstantWithNoValueIssue(String name, UID definition) {
		this.name = name;
		this.definition = definition;
	}

	public String getName() {
		return name;
	}

	public UID getDefinition() {
		return definition;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
