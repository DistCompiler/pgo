package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.util.Origin;

public class ProcedureNotFoundIssue extends Issue {

	private Origin origin;
	private String procedureName;

	public ProcedureNotFoundIssue(Origin origin, String name) {
		super();
		this.origin = origin;
		this.procedureName = name;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public String getProcedureName() {
		return procedureName;
	}

	public Origin getOrigin() {
		return origin;
	}
}
