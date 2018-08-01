package pgo.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Represents a parsing action that consumes tokens from a {@link LexicalContext} and either successfully
 * yields a result of type {@code Result} or fails with a {@link pgo.parser.ParseFailure}.
 * @param <Result> the type of an object representing a successful parse
 */
interface Grammar<Result> {

	/**
	 * Produces a further parsing action based on an existing parsing result.
	 * @param <Result> the type of the existing parsing result
	 * @param <ChainResult> the result type of the new parse action
	 */
	interface Operation<Result, ChainResult>{
		Grammar<ChainResult> perform(Result r);
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
	 * This method allows chaining of parse actions based on previous parsing results. Whenever a parse action fails,
	 * no further actions will be attempted and the failure will be propagated as a parse failure.
	 * @param operation An operation that depends on the result of the current parse action, returning a further parse
	 *                  action to be performed based on the result of the current parse action.
	 * @param <ChainResult> the type of the parse action returned by {@code operation.perform}
	 * @return a new parse action that yields the result of performing this parse action, followed by the parse action
	 * 	returned by {@code operation.perform(currentResult)}.
	 */
	default <ChainResult> Grammar<ChainResult> chain(Operation<Result, ChainResult> operation){
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
	}

	/**
	 * Transforms the result of one Grammar. Use this method when no further parsing needs to be done, but the
	 * format of the parsed data structure needs adjusting.
	 * @param operation a mapping from the actual parse result to an adjusted parse result
	 * @param <MapResult> the type of the mapped parse action
	 * @return a new parse action that yields the result of {@code operation.perform(originalResult)}
	 */
	default <MapResult> Grammar<MapResult> map(Mapping<Result, MapResult> operation){
		return resultMutator -> {
			Mutator<Result> parentResult = new Mutator<>();
			List<ParseAction> parentActions = getActions(parentResult);
			List<ParseAction> actions = new ArrayList<>(parentActions.size() + 1);
			actions.addAll(parentActions);
			actions.add(new ExecutorParseAction(() -> {
				resultMutator.setValue(operation.perform(parentResult.getValue()));
				return Collections.emptyList();
			}));
			return actions;
		};
	}

	/**
	 * A shorthand for generating parsing successes.
	 * @param result the result of this successful parse
	 * @param <Result> the type of the result
	 * @return a parse action that will always succeed, yielding {@code result}
	 */
	static <Result> Grammar<Result> success(Result result){
		return resultMutator -> Collections.singletonList(new ExecutorParseAction(() -> {
			resultMutator.setValue(result);
			return Collections.emptyList();
		}));
	}

	static <Result> Grammar<Result> failure(ParseFailure failure) {
		return resultMutator -> Collections.singletonList(new FailParseAction(failure));
	}

	/**
	 * Performs the parsing action, returning a result representing either a successful parse or a failure.
	 *
	 * FIXME
	 *
	 * @param resultMutator the Mutator to fill with the result of parsing this Grammar
	 * @return the result of attempting this parsing action
	 */
	List<ParseAction> getActions(MutatorInterface<? super Result> resultMutator);

	default Result parse(LexicalContext lexicalContext) throws TLAParseException {
		Mutator<Result> resultMutator = new Mutator<>();
		ParsingContext parsingContext = new ParsingContext(lexicalContext);
		ParseActionExecutor exec = new ParseActionExecutor(lexicalContext, parsingContext);
		parsingContext.preQueueActions(getActions(resultMutator));

		Optional<ParseAction> currentAction;
		while((currentAction = parsingContext.dequeueAction()).isPresent()) {
			if(!currentAction.get().accept(exec)){
				if(!parsingContext.backtrack()){
					throw new TLAParseException(parsingContext.getFailures());
				}
			}
		}

		return resultMutator.getValue();
	}
}
