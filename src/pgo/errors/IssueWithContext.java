package pgo.errors;

public class IssueWithContext extends Issue {
	Context context;
	Issue issue;
	
	public IssueWithContext(Issue issue, Context context) {
		this.issue = issue;
		this.context = context;
	}
	
	public Issue getIssue() {
		return issue;
	}
	
	public Context getContext() {
		return context;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
