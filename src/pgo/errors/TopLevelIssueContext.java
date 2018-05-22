package pgo.errors;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import pgo.formatters.IndentingWriter;
import pgo.formatters.IssueFormattingVisitor;

public class TopLevelIssueContext extends IssueContext {

	List<Issue> errors;
	
	public TopLevelIssueContext() {
		this.errors = new ArrayList<>();
	}
	
	@Override
	public void error(Issue err) {
		errors.add(err);
	}

	@Override
	public boolean hasErrors() {
		return !errors.isEmpty();
	}
	
	public List<Issue> getIssues(){
		return errors;
	}
	
	public void format(IndentingWriter out) throws IOException {
		out.write("Detected ");
		out.write(Integer.toString(errors.size()));
		out.write(" issue(s):");
		for(Issue e : errors) {
			out.newLine();
			e.accept(new IssueFormattingVisitor(out));
		}
	}

	public String format() {
		StringWriter w = new StringWriter();
		IndentingWriter out = new IndentingWriter(w);
		try {
			format(out);
		} catch (IOException e) {
			throw new RuntimeException("StringWriter should not throw IOException", e);
		}
		return w.toString();
	}
}
