package pgo.parser;

import pgo.util.SourceLocatable;

public abstract class ParseFailureVisitor<T, E extends Throwable> {
	public abstract T visit(ParseFailure.StringMatchFailure stringMatchFailure) throws E;
	public abstract T visit(ParseFailure.PatternMatchFailure patternMatchFailure) throws E;
	public abstract T visit(ParseFailure.EOFMatchFailure eofMatchFailure) throws E;
	public abstract <Result extends SourceLocatable> T visit(ParseFailure.RejectFailure<Result> rejectFailure) throws E;
}
