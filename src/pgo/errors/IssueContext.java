package pgo.errors;

public abstract class IssueContext {
	
	public abstract void error(Issue err);
	
	public abstract boolean hasErrors();
	
	public IssueContext withContext(Context context) {
		return new NestedIssueContext(this, context);
	}
}
