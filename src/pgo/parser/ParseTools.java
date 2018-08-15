package pgo.parser;

import java.util.*;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import pgo.util.SourceLocatable;

public final class ParseTools {
	
	private ParseTools() {}

	private static final Pattern WHITESPACE = Pattern.compile("\\s+");

	/**
	 * Returns a parse action that matches exactly the string token
	 * @param token the string to match
	 * @return the parse action, yielding the location at which the string was matched
	 */
	public static Grammar<Located<Void>> matchString(String token){
		return new StringGrammar(token);
	}

	/**
	 * Returns a parse action that matches exactly any one of the strings provided. Though this is trivially
	 * expressible as a combination of {@link ParseTools#matchString(String)} and {@link ParseTools#parseOneOf}, this
	 * is taken as a primitive for efficiency reasons.
	 * reasons of efficiency.
	 * @param options the set of strings to match
	 * @return the parse action, yielding which of the strings matched
	 */
	public static Grammar<Located<String>> matchStringOneOf(List<String> options){
		return parseOneOf(options
				.stream()
				.map(option -> matchString(option).map(v -> new Located<>(v.getLocation(), option)))
				.collect(Collectors.toList()));
	}

	/**
	 * Returns a parse action that matches the regex pattern given at the current position, using the semantics of
	 * {@link Matcher#lookingAt()}. The action yields the {@link MatchResult} on success.
	 * @param pattern the pattern to match
	 * @return the parse action
	 */
	public static Grammar<Located<MatchResult>> matchPattern(Pattern pattern){
		return new PatternGrammar(pattern);
	}

	/**
	 * Returns a parse action that matches and discards one or more characters of whitespace, defined as the regex
	 * class \s
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchWhitespace(){
		return matchPattern(WHITESPACE).map(res -> new Located<>(res.getLocation(), null));
	}

	public static final Variable<Integer> MIN_COLUMN = new Variable<>("MIN_COLUMN");

	/**
	 * Returns a parse action that behaves exactly like the provided action, but fails with
	 * {@link ParseFailure.InsufficientlyIndented} if the result is not indented at or beyond minColumn.
	 * @param action the action to perform
	 * @param <ParseResult> the result type of action
	 * @return the new parse action
	 */
	public static <ParseResult extends SourceLocatable> Grammar<ParseResult> checkMinColumn(
					Grammar<ParseResult> action){
		return action.filter(info -> info.getResult().getLocation().getStartColumn() >= info.get(MIN_COLUMN));
	}

	/**
	 * Combines parse actions from the list of options into one single parse action. Each action will be tried in the
	 * same order as in the list, and the first successful action's result will be yielded. PlusCalIf none of the actions match
	 * the entire set of parse failures will be yielded.
	 * @param options a list of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(
					List<Grammar<? extends Result>> options){
		return new BranchGrammar<>(options);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#parseOneOf(List< Grammar <? extends Result>)}.
	 * @param options an array of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	@SafeVarargs
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(
					Grammar<? extends Result>... options){
		return parseOneOf(Arrays.asList(options));
	}

	/**
	 * <p>Creates a parse action that repeatedly attempts the parse action element until it fails. The result of each
	 * attempt will be combined into a {@link pgo.parser.LocatedList}. This action has a similar behaviour to
	 * the Kleene star (*).</p>
	 *
	 * <p>
	 *     Note: the source locations of each element will be combined and presented as the location of the LocatedList
	 * </p>
	 * @param element the parse action to repeat
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the parse action
	 */
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeat(
					Grammar<Result> element){
		ReferenceGrammar<Located<ConsList<Result>>> recur = new ReferenceGrammar<>();
		recur.setReferencedGrammar(parseOneOf(
				emptySequence()
						.part(element)
						.part(recur)
				.map(seq ->
						new Located<>(
								seq.getLocation(),
								seq.getValue().getFirst().getValue().cons(seq.getValue().getRest().getFirst()))),
				nop().map(v -> new Located<>(v.getLocation(), new ConsList<>())))
		);

		return recur.map(seq -> new LocatedList<>(seq.getLocation(), seq.getValue().toList()));
	}

	/**
	 * Similar to {@link pgo.parser.ParseTools#repeat(Grammar <Result>)}, but only accepting sequences of at least one element.
	 * @param element a parse action representing one element of the list
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the parse action
	 */
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeatOneOrMore(Grammar<Result> element){
		Objects.requireNonNull(element);

		ReferenceGrammar<Located<ConsList<Result>>> recur = new ReferenceGrammar<>();
		recur.setReferencedGrammar(parseOneOf(
				emptySequence()
						.part(element)
						.part(recur)
						.map(seq ->
								new Located<>(
										seq.getLocation(),
										seq.getValue().getFirst().getValue().cons(seq.getValue().getRest().getFirst()))),
				nop().map(v -> new Located<>(v.getLocation(), new ConsList<>())))
		);

		return emptySequence()
				.part(element)
				.part(recur)
				.map(seq ->
						new LocatedList<>(
								seq.getLocation(),
								seq.getValue().getFirst().getValue()
										.cons(seq.getValue().getRest().getFirst()).toList()));
	}

	public static EmptySequenceGrammar emptySequence() { return new EmptySequenceGrammar(); }

	/**
	 * Creates a parse action that inverts the result of the given parse action.
	 * PlusCalIf the given action succeeds, this action fails. PlusCalIf the given action fails, this action succeeds.
	 * @param action the parse action to be inverted
	 * @return a parse action that will successfully parse anything that is rejected by the given action
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> reject(Grammar<Result> action){
		return new RejectGrammar<>(action);
	}

	/**
	 * <p>
	 * Useful for dealing with some subtleties of parse actions - for example, recursive parse actions (and thus
	 * recursive grammars) cannot be directly represented as they will consume infinite space. You can work around this
	 * by prefixing the recursive call with {@code nop()} like this: {@code nop().chain(v -> yourRecursiveCall(...))}.
	 * </p>
	 *
	 * <p>
	 * This ensures that the recursive parse action will only be instantiated upon control flow reaching the recursive
	 * call.
	 * </p>
	 *
	 * @return a parse action that successfully parses no tokens and yields null, located at the current parse location.
	 */
	public static Grammar<Located<Void>> nop() {
		return matchString("");
	}

	public static <T extends SourceLocatable> T readOrExcept(LexicalContext ctx, Grammar<T> grammar) throws ParseFailureException {
		Grammar<T> withEOF = emptySequence()
				.part(grammar)
				.drop(matchEOF())
				.map(seq -> seq.getValue().getFirst());

		return withEOF.parse(ctx);
	}

	public static Grammar<Located<Void>> matchEOF() {
		return new EOFGrammar();
	}

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseListOf(Grammar<AST> element, Grammar<? extends SourceLocatable> sep){
		return emptySequence()
				.part(element)
				.part(repeat(
						emptySequence()
								.drop(sep)
								.part(element)
								.map(seq -> seq.getValue().getFirst())
						))
				.map(seq -> {
					LocatedList<AST> result = new LocatedList<>(seq.getLocation(), new ArrayList<>());
					result.add(seq.getValue().getRest().getFirst());
					result.addAll(seq.getValue().getFirst());
					return result;
				});
	}

}
