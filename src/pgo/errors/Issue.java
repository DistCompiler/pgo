package pgo.errors;

public abstract class Issue {

	public Issue withContext(Context ctx) {
		return new IssueWithContext(this, ctx);
	}
	
	public abstract <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E;
	
}
