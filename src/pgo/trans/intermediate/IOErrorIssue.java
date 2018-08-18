package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;

import java.io.IOException;

public class IOErrorIssue extends Issue {
	
	IOException error;

	public IOErrorIssue(IOException e) {
		super();
		this.error = e;
	}
	
	public IOException getError() {
		return error;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
