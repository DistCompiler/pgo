package pgo.trans.passes.scope;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class NoModulesFoundInFileIssue extends Issue {

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
