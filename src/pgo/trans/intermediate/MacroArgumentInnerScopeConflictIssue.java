package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.TLAIdentifier;

public class MacroArgumentInnerScopeConflictIssue extends Issue {

	private TLAIdentifier id;

	public MacroArgumentInnerScopeConflictIssue(TLAIdentifier id) {
		this.id = id;
	}
	
	public TLAIdentifier getIdentifier() {
		return id;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
