package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

import java.nio.file.Path;
import java.util.List;

public class ModuleNotFoundIssue extends Issue {
	
	public String moduleName;
	public List<Path> pathsChecked;

	public ModuleNotFoundIssue(String moduleName, List<Path> pathsChecked) {
		super();
		this.moduleName = moduleName;
		this.pathsChecked = pathsChecked;
	}

	public String getModuleName() {
		return moduleName;
	}

	public List<Path> getPathsChecked() {
		return pathsChecked;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
