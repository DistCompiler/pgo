package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalInstance;

public class UnknownArchetypeTargetIssue extends Issue {
	private final ModularPlusCalInstance modularPlusCalInstance;

	public UnknownArchetypeTargetIssue(ModularPlusCalInstance modularPlusCalInstance) {
		this.modularPlusCalInstance = modularPlusCalInstance;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalInstance getModularPlusCalInstance() {
		return modularPlusCalInstance;
	}
}
