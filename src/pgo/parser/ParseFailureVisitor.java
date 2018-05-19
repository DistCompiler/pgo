package pgo.parser;

import pgo.parser.ParseFailure.InsufficientOperatorPrecedence;
import pgo.parser.ParseFailure.InsufficientlyIndented;
import pgo.parser.ParseFailure.NoBranchesMatched;
import pgo.parser.ParseFailure.UnexpectedBuiltinToken;
import pgo.parser.ParseFailure.UnexpectedEOF;
import pgo.parser.ParseFailure.UnexpectedTokenType;

public abstract class ParseFailureVisitor<T, E extends Throwable> {

	public abstract T visit(UnexpectedEOF unexpectedEOF) throws E;
	public abstract T visit(UnexpectedTokenType unexpectedTokenType) throws E;
	public abstract T visit(UnexpectedBuiltinToken unexpectedBuiltinToken) throws E;
	public abstract T visit(NoBranchesMatched noBranchesMatched) throws E;
	public abstract T visit(InsufficientlyIndented insufficientlyIndented) throws E;
	public abstract T visit(InsufficientOperatorPrecedence insufficientOperatorPrecedence) throws E;

}
