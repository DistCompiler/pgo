package pgo.trans.intermediate;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.parser.ParseFailure;

public class TLAParserIssue extends Issue {

	ParseFailure error;
	
	public TLAParserIssue(ParseFailure error) {
		this.error = error;
	}
	
	ParseFailure getError() {
		return error;
	}
	
	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
