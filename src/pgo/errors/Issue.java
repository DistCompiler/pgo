package pgo.errors;

import pgo.Unreachable;
import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;
import pgo.trans.PGoTransException;

import java.io.IOException;
import java.io.StringWriter;

public abstract class Issue extends PGoTransException {
	public Issue() {
		super("");
	}
	public Issue(String msg) {
		super(msg);
	}

	@Override
	public String getMessage() {
		StringWriter sw = new StringWriter();
		IndentingWriter out = new IndentingWriter(sw);
		try {
			accept(new IssueFormattingVisitor(out));
		} catch (IOException e) {
			throw new Unreachable(); // string ops don't throw IO exceptions
		}
		return sw.getBuffer().toString();
	}

	public Issue withContext(Context ctx) {
		return new IssueWithContext(this, ctx);
	}
	
	public abstract <T, E extends Throwable> T accept(IssueVisitor<T, E> v) throws E;
	
}
