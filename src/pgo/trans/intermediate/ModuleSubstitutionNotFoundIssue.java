package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.TLAIdentifier;

public class ModuleSubstitutionNotFoundIssue extends Issue {

	TLAIdentifier from;

	public ModuleSubstitutionNotFoundIssue(TLAIdentifier from) {
		this.from = from;
	}
	
	public TLAIdentifier getFrom() {
		return from;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
