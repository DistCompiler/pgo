package pgo.trans.passes.type;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.type.Type;
import pgo.scope.UID;

public class TypeInferenceFailureIssue extends Issue {
	private final UID uid;
	private final Type type;

	public TypeInferenceFailureIssue(UID uid, Type type) {
		this.uid = uid;
		this.type = type;
	}

	public UID getUID() {
		return uid;
	}

	public Type getType() {
		return type;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
