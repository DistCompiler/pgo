package pgo.trans.passes.validation;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalInstance;
import pgo.scope.UID;

public class VariableMappedMultipleTimesIssue extends Issue {
	private final UID varUID;
	private final ModularPlusCalInstance instance;

	public VariableMappedMultipleTimesIssue(UID varUID, ModularPlusCalInstance instance) {
        this.varUID = varUID;
        this.instance = instance;
	}

	public UID getVarUID() {
		return varUID;
	}

	public ModularPlusCalInstance getInstance() {
		return instance;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
