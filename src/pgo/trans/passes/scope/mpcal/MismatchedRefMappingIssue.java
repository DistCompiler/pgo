package pgo.trans.passes.scope.mpcal;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.model.mpcal.ModularPlusCalInstance;

import java.util.Set;

public class MismatchedRefMappingIssue extends Issue {
	private final ModularPlusCalInstance modularPlusCalInstance;
	private final Set<String> unmappedNames;

	public MismatchedRefMappingIssue(ModularPlusCalInstance modularPlusCalInstance, Set<String> unmappedNames) {
		this.modularPlusCalInstance = modularPlusCalInstance;
		this.unmappedNames = unmappedNames;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public ModularPlusCalInstance getModularPlusCalInstance() {
		return modularPlusCalInstance;
	}

	public Set<String> getUnmappedNames() {
		return unmappedNames;
	}
}
