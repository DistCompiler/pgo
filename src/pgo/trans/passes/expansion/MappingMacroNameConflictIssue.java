package pgo.trans.passes.expansion;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalMappingMacro;

public class MappingMacroNameConflictIssue extends Issue {
	private final ModularPlusCalMappingMacro first;
	private final ModularPlusCalMappingMacro second;

	public MappingMacroNameConflictIssue(ModularPlusCalMappingMacro first, ModularPlusCalMappingMacro second) {
		this.first = first;
		this.second = second;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalMappingMacro getFirst() {
		return first;
	}

	public ModularPlusCalMappingMacro getSecond() {
		return second;
	}
}
