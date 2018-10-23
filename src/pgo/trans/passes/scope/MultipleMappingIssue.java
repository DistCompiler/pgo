package pgo.trans.passes.scope;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalMapping;

public class MultipleMappingIssue extends Issue {
	private final ModularPlusCalMapping first;
	private final ModularPlusCalMapping second;

	public MultipleMappingIssue(ModularPlusCalMapping first, ModularPlusCalMapping second) {
        this.first = first;
        this.second = second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalMapping getFirst() {
		return first;
	}

	public ModularPlusCalMapping getSecond() {
		return second;
	}
}
