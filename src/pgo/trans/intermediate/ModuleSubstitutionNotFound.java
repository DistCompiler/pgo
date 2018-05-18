package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.tla.PGoTLAIdentifier;

public class ModuleSubstitutionNotFound extends Issue {

	PGoTLAIdentifier from;

	public ModuleSubstitutionNotFound(PGoTLAIdentifier from) {
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
