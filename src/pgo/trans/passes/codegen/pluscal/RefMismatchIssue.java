package pgo.trans.passes.codegen.pluscal;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.TLAExpression;

public class RefMismatchIssue extends Issue {
	private final PlusCalVariableDeclaration param;
	private final TLAExpression value;

	public RefMismatchIssue(PlusCalVariableDeclaration param, TLAExpression value) {
		this.param = param;
		this.value = value;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public PlusCalVariableDeclaration getParam() {
		return param;
	}

	public TLAExpression getValue() {
		return value;
	}
}
