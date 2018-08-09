package pgo.parser;

import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
		List<Grammar<? extends Located<String>>> compiledOptions = new ArrayList<>(options.size());
		for(String option : options) {
			compiledOptions.add(matchString(option).map(v -> new Located<>(v.getLocation(), option)));
		}
		return parseOneOf(compiledOptions);
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

	public static final Variable<Located<Integer>> MIN_COLUMN = new Variable<>("MIN_COLUMN");

	/**
	 * Returns a parse action that behaves exactly like the provided action, but fails with
	 * {@link ParseFailure.InsufficientlyIndented} if the result is not indented at or beyond minColumn.
	 * @param action the action to perform
	 * @param <ParseResult> the result type of action
	 * @return the new parse action
	 */
	public static <ParseResult extends SourceLocatable> Grammar<ParseResult> checkMinColumn(Grammar<ParseResult> action){
		return action.filter(info -> info.getResult().getLocation().getStartColumn() >= info.get(MIN_COLUMN).getValue());
	}

	/**
	 * Combines parse actions from the list of options into one single parse action. Each action will be tried in the
	 * same order as in the list, and the first successful action's result will be yielded. PlusCalIf none of the actions match
	 * the entire set of parse failures will be yielded.
	 * @param options a list of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(List<Grammar<? extends Result>> options){
		return new BranchGrammar<>(options);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#parseOneOf(List< Grammar <? extends Result>)}.
	 * @param options an array of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	@SafeVarargs
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(Grammar<? extends Result>... options){
		return parseOneOf(Arrays.asList(options));
	}

	public static <Result extends SourceLocatable> Grammar<Result> scope(Supplier<Grammar<Result>> fn) {
		return fn.get();
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
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeat(Grammar<Result> element){
		Variable<Located<ConsList<Result>>> rest = new Variable<>("rest");
		Variable<Result> currentElement = new Variable<>("currentElement");
		return ParseTools.<Located<ConsList<Result>>>fix(self -> parseOneOf(
						sequence(
								part(currentElement, element),
								part(rest, self)
						).map(seq -> {
							Result e = seq.get(currentElement);
							Located<ConsList<Result>> lst = seq.get(rest);
							return new Located<>(lst.getLocation().combine(e.getLocation()), lst.getValue().cons(e));
						}),
						nop().map(v -> new Located<>(v.getLocation(), new ConsList<>()))
		)).map(lst -> new LocatedList<>(lst.getLocation(), lst.getValue().toList()));
	}

	/**
	 * Similar to {@link pgo.parser.ParseTools#repeat(Grammar <Result>)}, but only accepting sequences of at least one element.
	 * @param element a parse action representing one element of the list
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the parse action
	 */
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeatOneOrMore(Grammar<Result> element){
		Objects.requireNonNull(element);

		Variable<Result> first = new Variable<>("first");
		Variable<LocatedList<Result>> rest = new Variable<>("rest");
		return sequence(
				part(first, element),
				part(rest, repeat(element))
				).map(seqResult -> {
					LocatedList<Result> r = seqResult.get(rest);
					Result f = seqResult.get(first);
					r.addLocation(f.getLocation());
					r.add(0, f);
					return r;
				});
	}

	/**
	 * <p>A tool for expressing a sequence of consecutive parse actions.</p>
	 *
	 * <p>In order to work better within the context of Java, we do some unusual things here. The sequence of actions
	 * is expressed as a series of {@link GrammarSequencePart} objects. Here is some example code:</p>
	 *
	 * <pre>{@code
	 * Variable<Result> mut = new Variable<>("mut");
	 *
	 * return sequence(
	 * 		drop(parseX()),
	 * 		part(mut, parseY()),
	 * 		drop(parseZ()
	 * ).map(result -> {
	 * 		return new ASTNode(result.getLocation(), mut.getValue());
	 * });
	 * }</pre>
	 *
	 * <p>
	 * In this example we create a parse action that accepts a sequence of X, Y and Z. The values of X and Z do not
	 * matter, perhaps as they are just built-in constants like punctuation. As such, we
	 * {@link pgo.parser.ParseTools#drop} them. They will still be required for parsing to succeed but
	 * their values are dropped. The item of interest, Y, does need storing so we indicate we are interested using
	 * {@link pgo.parser.ParseTools#part}. The result of parsing Y will be stored in the
	 * {@link pgo.parser.Variable} mut.
	 * </p>
	 *
	 * <p>
	 * Since for accurate source location tracking we want to know the location of everything we parsed,
	 * the sequence yields a {@link pgo.parser.ParseActionSequenceResult} which holds metadata
	 * for the entire parse including dropped elements, currently only the entire source location.
	 * </p>
	 *
	 * @param parts a list of parts of the sequence to parse
	 * @see pgo.parser.ParseTools#sequence(Grammar...)
	 * @return a parse action that will yield parse metadata for the entire sequence, use Variables and
	 * 		{@link Grammar#map} to transform this result into the desired data structure as described
	 * 		above.
	 */
	public static Grammar<ParseInfo<Located<Void>>> sequence(List<Grammar<Located<Void>>> parts){
		return new SequenceGrammar(parts);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#sequence(List< GrammarSequencePart)}
	 * @param parts an array of sequence parts, representing the sequence the parse action should recognise
	 * @return the parse action
	 */
	@SafeVarargs
	public static Grammar<ParseInfo<Located<Void>>> sequence(Grammar<Located<Void>>... parts){
		return new SequenceGrammar(Arrays.asList(parts));
	}

	/**
	 * Creates a {@link GrammarSequencePart}. This represents a part of the sequence that is of interest.
	 * @param variable the Variable in which to store the result of parsing this part of the sequence
	 * @param grammar the parse action to execute as this part of the sequence
	 * @param <Result> the type of the parse action's result (also the type of the Variable's value)
	 * @return a part of a parse action sequence
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> part(Variable<Result> variable, Grammar<Result> grammar){
		Objects.requireNonNull(variable);
		Objects.requireNonNull(grammar);
		return new AssignmentGrammar<>(variable, grammar);
	}

	public static <Result extends SourceLocatable> Grammar<Result> fix(Function<ReferenceGrammar<Result>, Grammar<Result>> fn) {
		return new FixPointGrammar<>(fn);
	}

	/**
	 * Creates a part of a sequence. This represents a part of a sequence that is not of
	 * interest but still part of the grammar like punctuation, brackets, etc...
	 *
	 * Executes the parse action then discards the result.
	 *
	 * @param action the parse action to execute
	 * @param <Result> the type of the discarded result
	 * @return a part of a parse action sequence
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> drop(Grammar<Result> action){
		return action.map(v -> new Located<>(v.getLocation(), null));
	}

	/**
	 * Creates a parse action that inverts the result of the given parse action.
	 * PlusCalIf the given action succeeds, this action fails. PlusCalIf the given action fails, this action succeeds.
	 * @param action the parse action to be inverted
	 * @return a parse action that will successfully parse anything that is rejected by the given action
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> reject(Grammar<Result> action){
		return new RejectGrammar<>(action);
	}

	public static <Result extends SourceLocatable> Grammar<Result> access(Function<ParseInfo<Located<Void>>, Result> accessor) {
		return sequence().map(accessor);
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
		Variable<T> result = new Variable<>("result");
		Grammar<T> withEOF = sequence(
				part(result, grammar),
				drop(matchEOF())
		).map(seqResult -> seqResult.get(result));

		return withEOF.parse(ctx);
	}

	public static Grammar<Located<Void>> matchEOF() {
		return new EOFGrammar();
	}

	public static <Result extends SourceLocatable> Grammar<Result> argument(Variable variable, Grammar<Result> grammar) {
		return new ArgumentGrammar<>(variable, grammar);
	}

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseListOf(Grammar<AST> element, Grammar<? extends SourceLocatable> sep){
		Variable<AST> first = new Variable<>("first");
		Variable<LocatedList<AST>> rest = new Variable<>("rest");
		return sequence(
				part(first, element),
				part(rest, repeat(
						scope(() -> {
							Variable<AST> pt = new Variable<>("pt");
							return sequence(
									drop(sep),
									part(pt, element)
							).map(seq -> seq.get(pt));
						})))
				).map(seq -> {
					LocatedList<AST> rst = seq.get(rest);
					AST fst = seq.get(first);
					rst.addLocation(fst.getLocation());
					rst.add(0, fst);
					return rst;
				});
	}

}
