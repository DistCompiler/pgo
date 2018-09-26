package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalArchetype;
import pgo.model.mpcal.ModularPlusCalInstance;

public class InstanceArgumentCountMismatchIssue extends Issue {
	private final ModularPlusCalInstance modularPlusCalInstance;
	private final ModularPlusCalArchetype modularPlusCalArchetype;

	public InstanceArgumentCountMismatchIssue(ModularPlusCalInstance modularPlusCalInstance,
	                                          ModularPlusCalArchetype modularPlusCalArchetype) {
		this.modularPlusCalInstance = modularPlusCalInstance;
		this.modularPlusCalArchetype = modularPlusCalArchetype;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalInstance getModularPlusCalInstance() {
		return modularPlusCalInstance;
	}

	public ModularPlusCalArchetype getModularPlusCalArchetype() {
		return modularPlusCalArchetype;
	}
}
