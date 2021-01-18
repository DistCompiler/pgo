package pgo.trans.passes.parse;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.parser.ParsingError;

public class ParsingIssue extends Issue {
	private final String language;
	private final ParsingError error;
	
	public ParsingIssue(String language, ParsingError error) {
		initCause(error);
		this.language = language;
		this.error = error;
	}
	
	public ParsingError getError() {
		return error;
	}

	public String getLanguage() { return language; }

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
