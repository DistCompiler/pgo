package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.PGoTLAIdentifier;

public class ModuleSubstitutionNotFoundIssue extends Issue {

	PGoTLAIdentifier from;

	public ModuleSubstitutionNotFoundIssue(PGoTLAIdentifier from) {
		this.from = from;
	}
	
	public PGoTLAIdentifier getFrom() {
		return from;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
