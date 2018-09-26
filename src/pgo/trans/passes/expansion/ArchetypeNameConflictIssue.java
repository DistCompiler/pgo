package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalArchetype;

public class ArchetypeNameConflictIssue extends Issue {
	private final ModularPlusCalArchetype first;
	private final ModularPlusCalArchetype second;

	public ArchetypeNameConflictIssue(ModularPlusCalArchetype first, ModularPlusCalArchetype second) {
		this.first = first;
		this.second = second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalArchetype getFirst() {
		return first;
	}

	public ModularPlusCalArchetype getSecond() {
		return second;
	}
}
