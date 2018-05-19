package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import pgo.parser.ParseFailure.InsufficientOperatorPrecedence;
import pgo.parser.ParseFailure.InsufficientlyIndented;
import pgo.parser.ParseFailure.NoBranchesMatched;
import pgo.parser.ParseFailure.UnexpectedBuiltinToken;
import pgo.parser.ParseFailure.UnexpectedEOF;
import pgo.parser.ParseFailure.UnexpectedTokenType;
import pgo.util.SourceLocation;

public class ParseFailureOrderingVisitor extends ParseFailureVisitor<Void, RuntimeException> {

	private SortedMap<SourceLocation, List<ParseFailure>> failures;
	
	public ParseFailureOrderingVisitor() {
		this.failures = new TreeMap<>((l1, l2) -> -l1.compareTo(l2));
	}
	
	public SortedMap<SourceLocation, List<ParseFailure>> getFailures(){
		return failures;
	}
	
	private void add(SourceLocation loc, ParseFailure f) {
		if(!failures.containsKey(loc)) {
			failures.put(loc, new ArrayList<>());
		}
		failures.get(loc).add(f);
	}
	
	@Override
	public Void visit(UnexpectedEOF unexpectedEOF) throws RuntimeException {
		add(SourceLocation.unknown(), unexpectedEOF);
		return null;
	}

	@Override
	public Void visit(UnexpectedTokenType unexpectedTokenType) throws RuntimeException {
		add(unexpectedTokenType.getSourceLocation(), unexpectedTokenType);
		return null;
	}

	@Override
	public Void visit(UnexpectedBuiltinToken unexpectedBuiltinToken) throws RuntimeException {
		add(unexpectedBuiltinToken.getActual().getLocation(), unexpectedBuiltinToken);
		return null;
	}

	@Override
	public Void visit(NoBranchesMatched noBranchesMatched) throws RuntimeException {
		for(ParseFailure f : noBranchesMatched.getFailures()) {
			f.accept(this);
		}
		return null;
	}

	@Override
	public Void visit(InsufficientlyIndented insufficientlyIndented) throws RuntimeException {
		add(insufficientlyIndented.getSourceLocation(), insufficientlyIndented);
		return null;
	}

	@Override
	public Void visit(InsufficientOperatorPrecedence insufficientOperatorPrecedence) throws RuntimeException {
		add(insufficientOperatorPrecedence.getSourceLocation(), insufficientOperatorPrecedence);
		return null;
	}
	
}
