package pgo.errors;

public class NestedIssueContext extends IssueContext {
	
	IssueContext parent;
	Context context;

	public NestedIssueContext(IssueContext parent, Context context) {
		this.parent = parent;
		this.context = context;
	}

	@Override
	public void error(Issue err) {
		parent.error(err.withContext(context));
	}

	@Override
	public boolean hasIssues() {
		return parent.hasIssues();
	}

}
