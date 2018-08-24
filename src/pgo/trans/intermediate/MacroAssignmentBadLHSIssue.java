package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.TLAExpression;

public class MacroAssignmentBadLHSIssue extends Issue {

	private final TLAExpression expression;

	public MacroAssignmentBadLHSIssue(TLAExpression expression) {
		this.expression = expression;
	}

	public TLAExpression getExpression() { return expression; }


	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
