package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.List;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * This class represents a strategy for parsing text into an object of type Result.
 * @param <Result> the type of an object representing a successful parse
 */
public abstract class Grammar<Result extends SourceLocatable> {

	/**
	 * Generates a further Grammar object that "maps" the output of this grammar to the output of {@param mapping}
	 * when applied to any objects yielded by the current grammar.
	 * @param mapping a mapping from the actual parse result to an adjusted parse result of type MappingResult
	 * @param <MappingResult> the result type of the new grammar
	 * @return an new grammar that yields the corresponding mapping
	 */
	public <MappingResult extends SourceLocatable> Grammar<MappingResult> map(Function<Result, MappingResult> mapping){
		return new MappingGrammar<>(this, mapping);
	}

	/**
	 * Generates a grammar that only succeeds if both this grammar succeeds and {@param predicate} succeeds. The
	 * predicate is provided with both the parser's current state (as last set by
	 * {@link AbstractSequenceGrammar#dependentPart(Grammar, Function)}) and the current parsing result.
	 * @param predicate the predicate to test
	 * @return a new grammar that implements the corresponding filter operation
	 */
	public Grammar<Result> filter(Predicate<ParseInfo<Result>> predicate) {
		return new PredicateGrammar<>(this, predicate);
	}

	/**
	 * A shorthand for generating parsing successes.
	 * @param result the result of this successful parse
	 * @param <Result> the type of the result
	 * @return a grammar that will always succeed with value {@param result}
	 */
	public static <Result extends SourceLocatable> Grammar<Result> success(Result result){
		return ParseTools.matchString("").map(v -> result);
	}

	/**
	 * Attempts to parse this grammar against the current state of the provided {@param lexicalContext}. If there
	 * exist one or more valid parses the first one will be returned. If no valid parses exist, a
	 * {@link ParseFailureException} will be thrown.
	 * @param lexicalContext the lexical context in which to attempt to parse this grammar
	 * @return the "first" result yielded by the grammar (if there is more than one valid parse)
	 * @throws ParseFailureException thrown if no valid parses exist, indicates the furthest error(s) encountered
	 * during unsuccessful parses
	 */
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

	/**
	 * Returns a list of all possible interpretations of the {@param lexicalContext}. This list may be empty if no
	 * valid parses exist.
	 * @param lexicalContext the context in which to evaluate this grammar
	 * @return a list of all valid parses in the provided {@param lexicalContext}
	 */
	@SuppressWarnings("unchecked")
	public List<Result> enumerate(LexicalContext lexicalContext) {
		GrammarExecuteVisitor visitor = new GrammarExecuteVisitor(
				lexicalContext, new VariableMap().freeze(), new TreeMap<>(), new GrammarExecuteVisitor.MemoizeTable());
		GrammarExecuteVisitor.ParsingResult parsingResult = accept(visitor);
		return parsingResult.getResults().stream().map(p -> (Result)p.getResult()).collect(Collectors.toList());
	}

	public abstract <GrammarResult, Except extends Throwable> GrammarResult accept(GrammarVisitor<GrammarResult, Except> visitor) throws Except;
}
