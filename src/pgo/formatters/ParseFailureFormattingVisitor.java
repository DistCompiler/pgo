package pgo.formatters;

import java.io.IOException;

import pgo.Unreachable;
import pgo.parser.ParseFailure;
import pgo.parser.ParseFailure.InsufficientOperatorPrecedence;
import pgo.parser.ParseFailure.InsufficientlyIndented;
import pgo.parser.ParseFailure.NoBranchesMatched;
import pgo.parser.ParseFailure.UnexpectedEOF;
import pgo.parser.ParseFailureVisitor;

public class ParseFailureFormattingVisitor extends ParseFailureVisitor<Void, IOException> {

	private IndentingWriter out;

	public ParseFailureFormattingVisitor(IndentingWriter out) {
		this.out = out;
	}

	@Override
	public Void visit(UnexpectedEOF unexpectedEOF) throws IOException {
		out.write("unexpected EOF");
		return null;
	}

	@Override
	public Void visit(NoBranchesMatched noBranchesMatched) throws IOException {
		throw new Unreachable();
	}

	@Override
	public Void visit(InsufficientlyIndented insufficientlyIndented) throws IOException {
		out.write("token not parseable due to insufficient indentation; minimum indentation was ");
		out.write(Integer.toString(insufficientlyIndented.getMinColumn()));
		return null;
	}

	@Override
	public Void visit(InsufficientOperatorPrecedence insufficientOperatorPrecedence) throws IOException {
		out.write("operator with insufficient precedence encountered: actual precedence ");
		out.write(Integer.toString(insufficientOperatorPrecedence.getActualPrecedence()));
		out.write("; required precedence ");
		out.write(Integer.toString(insufficientOperatorPrecedence.getRequiredPrecedence()));
		return null;
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
	public Void visit(ParseFailure.ParseSuccess parseSuccess) throws IOException {
		out.write("parse success");
		return null;
	}

}
