package pgo.trans.passes.tlaparse;

import pgo.errors.Issue;
import pgo.errors.IssueVisitor;
import pgo.lexer.PGoTLALexerException;

public class TLALexerIssue extends Issue {
	
	PGoTLALexerException error;

	public TLALexerIssue(PGoTLALexerException error) {
		super();
		this.error = error;
	}
	
	public PGoTLALexerException getError() {
		return error;
	}

	@Override
	public <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
