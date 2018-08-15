package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.HashMap;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Represents a parsing action that consumes tokens from a {@link LexicalContext} and either successfully
 * yields a result of type {@code Result} or fails with a {@link pgo.parser.ParseFailure}.
 * @param <Result> the type of an object representing a successful parse
 */
public abstract class Grammar<Result extends SourceLocatable> {

	/**
	 * Transforms the result of one Grammar. Use this method when no further parsing needs to be done, but the
	 * format of the parsed data structure needs adjusting.
	 * @param operation a mapping from the actual parse result to an adjusted parse result
	 * @param <MapResult> the type of the mapped parse action
	 * @return a new parse action that yields the result of {@code operation.perform(originalResult)}
	 */
	public <MappingResult extends SourceLocatable> Grammar<MappingResult> map(Function<Result, MappingResult> mapping){
		return new MappingGrammar<>(this, mapping);
	}

	public Grammar<Result> filter(Predicate<ParseInfo<Result>> predicate) {
		return new PredicateGrammar<>(this, predicate);
	}

	/**
	 * A shorthand for generating parsing successes.
	 * @param result the result of this successful parse
	 * @param <Result> the type of the result
	 * @return a parse action that will always succeed, yielding {@code result}
	 */
	static <Result extends SourceLocatable> Grammar<Result> success(Result result){
		return ParseTools.matchString("").map(v -> result);
	}

	public Result parse(LexicalContext lexicalContext) throws ParseFailureException {
		GrammarExecuteVisitor visitor = new GrammarExecuteVisitor(
				lexicalContext, new VariableMap().freeze(), new TreeMap<>(), new HashMap<>());
		GrammarExecuteVisitor.ParsingResult parsingResult = accept(visitor);
		if(parsingResult.getResult() == null) {
			throw new ParseFailureException(visitor.getFailures());
		}else{
			return (Result)parsingResult.getResult();
		}
	}

	public abstract <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except;
}
