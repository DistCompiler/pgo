package pgo.parser;

import pgo.util.Mutator;
import pgo.util.SourceLocatable;

import java.util.Objects;

public class ReferenceGrammar<Result extends SourceLocatable> extends Grammar<Result> {

	private Mutator<Grammar<Result>> referencedGrammar;

	@Override
	public String toString() {
		return "REF";
	}

	public ReferenceGrammar() {
		this.referencedGrammar = new Mutator<>();
	}

	public ReferenceGrammar(Grammar<Result> referencedGrammar) {
		Objects.requireNonNull(referencedGrammar);
		this.referencedGrammar = new Mutator<>(referencedGrammar);
	}

	public void setReferencedGrammar(Grammar<Result> referencedGrammar) {
		Objects.requireNonNull(referencedGrammar);
		this.referencedGrammar.setValue(referencedGrammar);
	}

	public Grammar<Result> getReferencedGrammar() { return referencedGrammar.getValue(); }

	@Override
	public <Result1, Except extends Throwable> Result1 accept(GrammarVisitor<Result1, Except> visitor) throws Except {
		return visitor.visit(this);
	}
}
