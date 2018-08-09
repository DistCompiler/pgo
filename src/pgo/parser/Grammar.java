package pgo.parser;

import pgo.util.SourceLocatable;

import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Represents a parsing action that consumes tokens from a {@link LexicalContext} and either successfully
 * yields a result of type {@code Result} or fails with a {@link pgo.parser.ParseFailure}.
 * @param <Result> the type of an object representing a successful parse
 */
public abstract class Grammar<Result extends SourceLocatable> {

	/**
	 * This method allows chaining of parse actions based on previous parsing results. Whenever a parse action fails,
	 * no further actions will be attempted and the failure will be propagated as a parse failure.
	 * @param operation An operation that depends on the result of the current parse action, returning a further parse
	 *                  action to be performed based on the result of the current parse action.
	 * @param <ChainResult> the type of the parse action returned by {@code operation.perform}
	 * @return a new parse action that yields the result of performing this parse action, followed by the parse action
	 * 	returned by {@code operation.perform(currentResult)}.
	 */
	/*default <ChainResult> Grammar<ChainResult> chain(Operation<Result, ChainResult> operation){
		return resultMutator -> {
			Mutator<Result> parentResult = new Mutator<>();
			List<ParseAction> parentActions = this.getActions(parentResult);
			List<ParseAction> actions = new ArrayList<>(parentActions.size() + 1);
			actions.addAll(parentActions);
			actions.add(new ExecutorParseAction(() ->
					operation.perform(parentResult.getValue()).getActions(resultMutator)
			));
			return actions;
		};
	}*/

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

	static <Result extends SourceLocatable> Grammar<Result> failure(ParseFailure failure) {
		return null;
	}

	public CompiledGrammar<Result> compile() {
		GrammarCompileVisitor<Result> v = new GrammarCompileVisitor<>();
		accept(v);
		return v.getCompiledGrammar();
	}

	public Result parse(LexicalContext lexicalContext) throws ParseFailureException {
		return compile().parse(lexicalContext);
	}

	public abstract <Result, Except extends Throwable> Result accept(GrammarVisitor<Result, Except> visitor) throws Except;
}
