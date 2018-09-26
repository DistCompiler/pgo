package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalMapping;

public class UnknownMappingTargetIssue extends Issue {
	private final ModularPlusCalMapping modularPlusCalMapping;

	public UnknownMappingTargetIssue(ModularPlusCalMapping modularPlusCalMapping) {
		this.modularPlusCalMapping = modularPlusCalMapping;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalMapping getModularPlusCalMapping() {
		return modularPlusCalMapping;
	}
}
