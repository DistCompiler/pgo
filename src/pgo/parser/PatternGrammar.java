package pgo.parser;

import java.util.regex.MatchResult;
import java.util.regex.Pattern;

public class PatternGrammar extends Grammar<Located<MatchResult>> {

	private Pattern pattern;

	public PatternGrammar(Pattern pattern) {
		this.pattern = pattern;
	}

	@Override
	public String toString() {
		return "PATTERN "+pattern;
	}

	public Pattern getPattern() { return pattern; }

	@Override
	public <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
