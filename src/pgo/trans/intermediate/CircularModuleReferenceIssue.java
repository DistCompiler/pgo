package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

public class CircularModuleReferenceIssue extends Issue {
	
	private String moduleName;

	public CircularModuleReferenceIssue(String moduleName) {
		super();
		this.moduleName = moduleName;
	}

	public String getModuleName() {
		return moduleName;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
