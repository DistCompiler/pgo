package pgo.trans.passes.parse.tla;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.parser.ParseFailure;
import pgo.util.SourceLocation;

import java.util.NavigableMap;
import java.util.Set;

public class ParsingIssue extends Issue {

	private String language;
	private NavigableMap<SourceLocation, Set<ParseFailure>> error;
	
	public ParsingIssue(String language, NavigableMap<SourceLocation, Set<ParseFailure>> error) {
		this.language = language;
		this.error = error;
	}
	
	public NavigableMap<SourceLocation, Set<ParseFailure>> getError() {
		return error;
	}

	public String getLanguage() { return language; }

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
