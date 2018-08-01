package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;

public final class PatternParseAction extends ParseAction {

	private Pattern toMatch;
	private List<MutatorInterface<? super Located<MatchResult>>> resultMutators;

	public PatternParseAction(Pattern toMatch, MutatorInterface<? super Located<MatchResult>> resultMutator){
		this.toMatch = toMatch;
		this.resultMutators = new ArrayList<>();
		this.resultMutators.add(resultMutator);
	}

	@Override
	public String toString(){
		return "MATCH "+toMatch;
	}

	public Pattern getToMatch() { return toMatch; }
	public List<MutatorInterface<? super Located<MatchResult>>> getResultMutators() { return resultMutators; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean mergeCompatible(ParseAction other) {
		return other instanceof PatternParseAction && toMatch.equals(((PatternParseAction)other).toMatch);
	}

	@Override
	protected void mergeImpl(ParseAction other) {
		resultMutators.addAll(((PatternParseAction)other).resultMutators);
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
