package pgo.parser;

/**
 * Represents a parsing action that consumes tokens from a {@link pgo.parser.ParseContext} and either successfully
 * yields a result of type {@code Result} or fails with a {@link pgo.parser.ParseFailure}.
 * @param <Result> the type of an object representing a successful parse
 */
interface ParseAction<Result> {

	/**
	 * Produces a further parsing action based on an existing parsing result.
	 * @param <Result> the type of the existing parsing result
	 * @param <ChainResult> the result type of the new parse action
	 */
	interface Operation<Result, ChainResult>{
		ParseAction<ChainResult> perform(Result r);
	}

	/**
	 * A direct mapping between one parsing result and another.
	 * @param <Result> the type of the original parse result
	 * @param <ChainResult> the type of the transformed parse result
	 */
	interface Mapping<Result, ChainResult>{
		ChainResult perform(Result r);
	}

	/**
	 * Produces an {@link pgo.parser.ActionContext} as part of mechanism defined by
	 * {@link pgo.parser.ParseAction#withContext}
	 */
	interface ContextGenerator{
		ActionContext getContext();
	}

	/**
	 * This method allows chaining of parse actions based on previous parsing results. Whenever a parse action fails,
	 * no further actions will be attempted and the failure will be propagated as a parse failure.
	 * @param operation An operation that depends on the result of the current parse action, returning a further parse
	 *                  action to be performed based on the result of the current parse action.
	 * @param <ChainResult> the type of the parse action returned by {@code operation.perform}
	 * @return a new parse action that yields the result of performing this parse action, followed by the parse action
	 * 	returned by {@code operation.perform(currentResult)}.
	 */
	default <ChainResult> ParseAction<ChainResult> chain(Operation<Result, ChainResult> operation){
		return new ParseActionChain<>(this, operation);
	}

	/**
	 * Transforms the result of one ParseAction. Use this method when no further parsing needs to be done, but the
	 * format of the parsed data structure needs adjusting.
	 * @param operation a mapping from the actual parse result to an adjusted parse result
	 * @param <MapResult> the type of the mapped parse action
	 * @return a new parse action that yields the result of {@code operation.perform(originalResult)}
	 */
	default <MapResult> ParseAction<MapResult> map(Mapping<Result, MapResult> operation){
		return chain(result -> success(operation.perform(result)));
	}

	/**
	 * A shorthand for calling {@link pgo.parser.ParseAction#withContext(ContextGenerator)} with {@code () -> ctx}. Use this when the
	 * context does not depend on the results of executing previous parse actions.
	 * @param ctx the action's context
	 * @return a new parse action with the context ctx
	 */
	default ParseAction<Result> withContext(ActionContext ctx){
		return withContext(() -> ctx);
	}

	/**
	 * The longhand form of {@link pgo.parser.ParseAction#withContext(ActionContext)}, when the parsing context depends
	 * on information only available during parsing, not before.
	 * @param gen produces a context
	 * @return a new parse action that will have the context created by gen. {@code gen.getContext()} will be called
	 * 	at parse-time, allowing the context to depend on any previously executed parse actions
	 */
	default ParseAction<Result> withContext(ContextGenerator gen){
		return new ParseActionWithContext<>(this, gen);
	}

	/**
	 * A shorthand for generating parsing successes.
	 * @param result the result of this successful parse
	 * @param <Result> the type of the result
	 * @return a parse action that will always succeed, yielding {@code result}
	 */
	static <Result> ParseAction<Result> success(Result result){
		return new ParseActionSuccess<>(result);
	}

	/**
	 * A shorthand for generating parsing failures.
	 * @param failure an object describing the parsing failure
	 * @param <Result> the type of the expected parsing result (which will never be yielded)
	 * @return a parse action that always fails with error {@code failure}
	 */
	static <Result> ParseAction<Result> failure(ParseFailure failure) {
		return new ParseActionFailure<>(failure);
	}

	/**
	 * Performs the parsing action, returning a result representing either a successful parse or a failure.
	 *
	 * This would typically be used either internally or as a top-level call to initiate parsing once a tree of parsing
	 * actions has been fully constructed.
	 *
	 * @param ctx the parsing context on which to operate
	 * @return the result of attempting this parsing action
	 */
	ParseResult<Result> perform(ParseContext ctx);
}
