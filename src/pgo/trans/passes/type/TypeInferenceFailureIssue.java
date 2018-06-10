package pgo.trans.passes.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.type.PGoType;
import pgo.scope.UID;

public class TypeInferenceFailureIssue extends Issue {
	private UID uid;
	private PGoType type;

	public TypeInferenceFailureIssue(UID uid, PGoType type) {
		this.uid = uid;
		this.type = type;
	}

	public UID getUID() {
		return uid;
	}

	public PGoType getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
