package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.PGoTLAIdentifier;

public class MacroArgumentInnerScopeConflictIssue extends Issue {

	private PGoTLAIdentifier id;

	public MacroArgumentInnerScopeConflictIssue(PGoTLAIdentifier id) {
		this.id = id;
	}
	
	public PGoTLAIdentifier getIdentifier() {
		return id;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
