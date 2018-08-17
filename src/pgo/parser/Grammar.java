package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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

	@SuppressWarnings("unchecked")
	public Result parse(LexicalContext lexicalContext) throws ParseFailureException {
		GrammarExecuteVisitor visitor = new GrammarExecuteVisitor(
				lexicalContext, new VariableMap().freeze(), new TreeMap<>(), new GrammarExecuteVisitor.MemoizeTable());
		GrammarExecuteVisitor.ParsingResult parsingResult = accept(visitor);
		if(parsingResult.getResults().isEmpty()) {
			throw new ParseFailureException(visitor.getFailures());
		}else{
			lexicalContext.restore(parsingResult.getResults().get(0).getMark());
			return (Result)parsingResult.getResults().get(0).getResult();
		}
	}

	@SuppressWarnings("unchecked")
	public List<Result> enumerate(LexicalContext lexicalContext) {
		GrammarExecuteVisitor visitor = new GrammarExecuteVisitor(
				lexicalContext, new VariableMap().freeze(), new TreeMap<>(), new GrammarExecuteVisitor.MemoizeTable());
		GrammarExecuteVisitor.ParsingResult parsingResult = accept(visitor);
		return parsingResult.getResults().stream().map(p -> (Result)p.getResult()).collect(Collectors.toList());
	}

	public abstract <GrammarResult, Except extends Throwable> GrammarResult accept(GrammarVisitor<GrammarResult, Except> visitor) throws Except;
}
