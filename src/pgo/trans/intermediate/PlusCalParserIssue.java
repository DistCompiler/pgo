package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class PlusCalParserIssue extends Issue {
	private String message;

	public PlusCalParserIssue(String message) {
		this.message = message;
	}

	public String getMessage() {
		return message;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
