package pgo.formatters;

import java.io.IOException;

import pgo.parser.ParseFailure.InsufficientOperatorPrecedence;
import pgo.parser.ParseFailure.InsufficientlyIndented;
import pgo.parser.ParseFailure.NoBranchesMatched;
import pgo.parser.ParseFailure.UnexpectedBuiltinToken;
import pgo.parser.ParseFailure.UnexpectedEOF;
import pgo.parser.ParseFailure.UnexpectedTokenType;
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
	public Void visit(UnexpectedTokenType unexpectedTokenType) throws IOException {
		out.write("unexpected token of type ");
		out.write(unexpectedTokenType.getTokenType().toString());
		out.write("; expected ");
		out.write(unexpectedTokenType.getExpectedTokenType().toString());
		return null;
	}

	@Override
	public Void visit(UnexpectedBuiltinToken unexpectedBuiltinToken) throws IOException {
		out.write("unexpected builtin token \"");
		out.write(unexpectedBuiltinToken.getActual().getValue());
		out.write("\", expected one of [");
		boolean first = true;
		for(String opt : unexpectedBuiltinToken.getOptions()) {
			if(first) {
				first = false;
			}else {
				out.write(", ");
			}
			out.write(opt);
		}
		out.write("]");
		return null;
	}

	@Override
	public Void visit(NoBranchesMatched noBranchesMatched) throws IOException {
		throw new RuntimeException("unreachable");
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

}
