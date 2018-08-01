package pgo.parser;

import pgo.parser.ParseFailure.InsufficientOperatorPrecedence;
import pgo.parser.ParseFailure.InsufficientlyIndented;
import pgo.parser.ParseFailure.UnexpectedEOF;

public abstract class ParseFailureVisitor<T, E extends Throwable> {

	public abstract T visit(UnexpectedEOF unexpectedEOF) throws E;
	public abstract T visit(InsufficientlyIndented insufficientlyIndented) throws E;
	public abstract T visit(InsufficientOperatorPrecedence insufficientOperatorPrecedence) throws E;
	public abstract T visit(ParseFailure.StringMatchFailure stringMatchFailure) throws E;
	public abstract T visit(ParseFailure.PatternMatchFailure patternMatchFailure) throws E;
	public abstract T visit(ParseFailure.ParseSuccess parseSuccess) throws E;
}
