package pgo.trans.passes.tlaparse;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.parser.ParseFailure;
import pgo.util.SourceLocation;

import java.util.NavigableMap;
import java.util.Set;

public class TLAParserIssue extends Issue {

	private NavigableMap<SourceLocation, Set<ParseFailure>> error;
	
	public TLAParserIssue(NavigableMap<SourceLocation, Set<ParseFailure>> error) {
		this.error = error;
	}
	
	public NavigableMap<SourceLocation, Set<ParseFailure>> getError() {
		return error;
	}
	
	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
