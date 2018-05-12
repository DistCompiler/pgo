package pgo.parser;

import java.util.List;

import pgo.util.SourceLocation;

public class ParseFailure {
	
	public static class UnexpectedEOF extends ParseFailure {
		
	}
	
	public static UnexpectedEOF unexpectedEOF() {
		return new UnexpectedEOF();
	}
	
	public static class UnexpectedTokenType extends ParseFailure {
		int tokenType;
		SourceLocation sourceLocation;
		
		public UnexpectedTokenType(int tokenType, SourceLocation sourceLocation) {
			this.tokenType = tokenType;
			this.sourceLocation = sourceLocation;
		}
	}
	
	public static UnexpectedTokenType unexpectedTokenType(int tokenType, SourceLocation sourceLocation) {
		return new UnexpectedTokenType(tokenType, sourceLocation);
	}
	
	public static class UnexpectedBuiltinToken extends ParseFailure {
		LocatedString actual;
		List<String> options;
		
		public UnexpectedBuiltinToken(LocatedString actual, List<String> options) {
			this.actual = actual;
			this.options = options;
		}
	}
	
	public static UnexpectedBuiltinToken unexpectedBuiltinToken(LocatedString actual, List<String> options) {
		return new UnexpectedBuiltinToken(actual, options);
	}
	
	public static class NoBranchesMatched extends ParseFailure {
		List<ParseFailure> failures;

		public NoBranchesMatched(List<ParseFailure> failures) {
			this.failures = failures;
		}
	}

	public static NoBranchesMatched noBranchesMatched(List<ParseFailure> failures) {
		return new NoBranchesMatched(failures);
	}
	
	public static class InsufficientlyIndented extends ParseFailure {
		int actualColumn;
		int minColumn;
		SourceLocation sourceLocation;
		public InsufficientlyIndented(int actualColumn, int minColumn, SourceLocation sourceLocation) {
			super();
			this.actualColumn = actualColumn;
			this.minColumn = minColumn;
			this.sourceLocation = sourceLocation;
		}
	}

	public static InsufficientlyIndented insufficientlyIndented(int actualColumn, int minColumn, SourceLocation sourceLocation) {
		return new InsufficientlyIndented(actualColumn, minColumn, sourceLocation);
	}
	
	public static class InsufficientOperatorPrecedence extends ParseFailure{
		int actualPrecedence;
		int requiredPrecedence;
		SourceLocation sourceLocation;
		public InsufficientOperatorPrecedence(int actualPrecedence, int requiredPrecedence,
				SourceLocation sourceLocation) {
			this.actualPrecedence = actualPrecedence;
			this.requiredPrecedence = requiredPrecedence;
			this.sourceLocation = sourceLocation;
		}
	}
	
	public static InsufficientOperatorPrecedence insufficientOperatorPrecedence(int actualPrecedence, int requiredPrecedence, SourceLocation sourceLocation) {
		return new InsufficientOperatorPrecedence(actualPrecedence, requiredPrecedence, sourceLocation);
	}

}
