package pgo.formatters;

import pgo.parser.ParseFailure;
import pgo.parser.ParseFailureVisitor;

import java.io.IOException;

public class ParseFailureFormattingVisitor extends ParseFailureVisitor<Void, IOException> {

	private IndentingWriter out;

	public ParseFailureFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(ParseFailure.StringMatchFailure stringMatchFailure) throws IOException {
		out.write("failed to match string \""+stringMatchFailure.getString()+"\"");
		return null;
	}

	@Override
	public Void visit(ParseFailure.PatternMatchFailure patternMatchFailure) throws IOException {
		out.write("failed to match pattern "+patternMatchFailure.getPattern());
		return null;
	}

	@Override
	public Void visit(ParseFailure.EOFMatchFailure eofMatchFailure) throws IOException {
		out.write("failed to match EOF");
		return null;
	}

	@Override
	public Void visit(ParseFailure.RejectFailure rejectFailure) throws IOException {
		out.write("failed to reject "+rejectFailure.getToReject());
		return null;
	}

}
