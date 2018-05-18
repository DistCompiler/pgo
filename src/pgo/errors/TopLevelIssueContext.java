package pgo.errors;

import java.util.ArrayList;
import java.util.List;

public class TopLevelIssueContext extends IssueContext {

	List<Issue> errors;
	
	public TopLevelIssueContext() {
		this.errors = new ArrayList<>();
	}
	
	@Override
	public void error(Issue err) {
		errors.add(err);
	}

	@Override
	public boolean hasIssues() {
		return !errors.isEmpty();
	}
	
}
