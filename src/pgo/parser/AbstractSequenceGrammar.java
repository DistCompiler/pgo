package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.function.Function;

public abstract class AbstractSequenceGrammar<Sequence extends EmptyHeterogenousList> extends Grammar<Located<Sequence>> {

	public <Result extends SourceLocatable> PartSequenceGrammar<Result, Sequence> part(Grammar<Result> grammar) {
		return new PartSequenceGrammar<>(this, grammar);
	}

	public <Dropped extends SourceLocatable> DropSequenceGrammar<Dropped, Sequence> drop(Grammar<Dropped> grammar) {
		return new DropSequenceGrammar<>(this, grammar);
	}

	public <Result extends SourceLocatable> CallGrammar<Result, Sequence> dependentPart(
			Grammar<Result> grammar, Function<ParseInfo<Located<Sequence>>, VariableMap> mappingGenerator) {
		return new CallGrammar<>(this, grammar, mappingGenerator);
	}

}
