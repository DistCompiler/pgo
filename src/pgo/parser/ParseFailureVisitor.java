package pgo.parser;

public abstract class ParseFailureVisitor<T, E extends Throwable> {
	public abstract T visit(ParseFailure.StringMatchFailure stringMatchFailure) throws E;
	public abstract T visit(ParseFailure.PatternMatchFailure patternMatchFailure) throws E;
	public abstract T visit(ParseFailure.EOFMatchFailure eofMatchFailure) throws E;
	public abstract T visit(ParseFailure.RejectFailure rejectFailure) throws E;
}
