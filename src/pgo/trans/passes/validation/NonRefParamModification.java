package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.scope.UID;

public class NonRefParamModification extends Issue {
	private final UID declarationUID;

	public NonRefParamModification(UID declarationUID) {
		this.declarationUID = declarationUID;
	}

	public UID getDeclarationUID() {
		return declarationUID;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
