package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.List;

public final class GrammarSequencePart {

	private static class Pair<Result extends SourceLocatable> {
		private Mutator<Result> mutator;
		private Grammar<Result> grammar;

		public Pair(Mutator<Result> mutator, Grammar<Result> grammar) {
			this.mutator = mutator;
			this.grammar = grammar;
		}

		public SourceLocation getLocation() {
			return mutator.hasValue() ? mutator.getValue().getLocation() : SourceLocation.unknown();
		}

		public List<ParseAction> getActions() { return grammar.getActions(mutator); }
	}

	private Pair<? extends SourceLocatable> pair;

	public <Result extends SourceLocatable> GrammarSequencePart(Mutator<Result> mutator, Grammar<Result> grammar) {
		this.pair = new Pair<>(mutator, grammar);
	}

	public SourceLocation getLocation() {
		return pair.getLocation();
	}

	public List<ParseAction> getActions() {
		return pair.getActions();
	}
}
