package pgo.parser;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import pgo.util.ConsList;
import pgo.util.SourceLocatable;

public final class ParseTools {
	
	private ParseTools() {}

	public static final Pattern WHITESPACE = Pattern.compile("\\s+");

	/**
	 * Returns a grammar that matches exactly the string {@param token}
	 * @param token the string to match
	 * @return the grammar, yielding Void located at the range of text matched
	 */
	public static Grammar<Located<Void>> matchString(String token){
		return new StringGrammar(token);
	}

	/**
	 * Returns a grammar that matches any one of the string in {@param options}, in the order in which they appear
	 * in the list. This can be important if some of the strings are prefixes of each other like
	 * {@code Arrays.asList("variable", "variables")}
	 * @param options the list of strings to match
	 * @return the grammar, yielding a located string indicating which of the strings matched at what location
	 * in the text
	 */
	public static Grammar<Located<String>> matchStringOneOf(List<String> options){
		return parseOneOf(options
				.stream()
				.map(option -> matchString(option).map(v -> new Located<>(v.getLocation(), option)))
				.collect(Collectors.toList()));
	}

	/**
	 * Returns a grammar that matches the regular expression {@param pattern}. The match will only be valid at the
	 * current text position. Semantically the regular expression is checked using {@link Matcher#lookingAt()}.
	 * @param pattern the pattern to match
	 * @return a grammar yielding a located instance of {@link MatchResult}
	 */
	public static Grammar<Located<MatchResult>> matchPattern(Pattern pattern){
		return new PatternGrammar(pattern);
	}

	/**
	 * Returns a grammar that matches one or more instances of whitespace, defined as the regex {@code \s+}
	 * @return a grammar yielding the location of the matched whitespace
	 */
	public static Grammar<Located<Void>> matchWhitespace(){
		return matchPattern(WHITESPACE).map(res -> new Located<>(res.getLocation(), null));
	}

	/**
	 * A variable representing the least column at which a TLA+ token must be located in order for parsing
	 * of that token to succeed. If this is not present in the parsing state when trying to evaluate anything
	 * that uses {@link ParseTools#checkMinColumn}, the parser will crash. You can set it to -1 using
	 * {@link AbstractSequenceGrammar#dependentPart(Grammar, Function)}.
	 */
	public static final Variable<Integer> MIN_COLUMN = new Variable<>("MIN_COLUMN");

	/**
	 * Wraps the provided {@param grammar} with a check that the parsed result is located at a text column greater or equal to
	 * the value stored at {@link ParseTools#MIN_COLUMN} in the parsing state.
	 * @param grammar the grammar to wrap
	 * @param <ParseResult> the result type of the wrapped grammar
	 * @return the same grammar as provided, but {@link Grammar#filter(Predicate)}ed according to the MIN_COLUMN check
	 */
	public static <ParseResult extends SourceLocatable> Grammar<ParseResult> checkMinColumn(
					Grammar<ParseResult> grammar){
		return grammar.filter(info -> info.getResult().getLocation().getStartColumn() >= info.get(MIN_COLUMN));
	}

	/**
	 * Combines all the grammars in {@param options} such that the resulting grammar yields all valid parses of each
	 * grammar in sequence. In an unambiguous grammar this just means that the successful parse will be chosen,
	 * but can lead to multiple results if more than one branch is successful. Successful results will be yielded
	 * from each grammar in first to last order.
	 * @param options the list of grammars to combine
	 * @param <Result> the common result type of all the grammars
	 * @return a grammar yielding all successful results of the grammars in {@param options}
	 */
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(
					List<Grammar<? extends Result>> options){
		return new BranchGrammar<>(options);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#parseOneOf(List< Grammar <? extends Result>)}.
	 * @param options an array of grammars to merge
	 * @param <Result> the common result type of all the grammars
	 * @return the combined grammar
	 */
	@SafeVarargs
	public static <Result extends SourceLocatable> Grammar<Result> parseOneOf(
					Grammar<? extends Result>... options){
		return parseOneOf(Arrays.asList(options));
	}

	/**
	 * Creates a grammar that will parse any number of repetitions of the parameter {@param element}. In order to
	 * support correct backtracking, this grammar will yield all possible numbers of repetitions from longest to
	 * shortest (empty sequence). If you don't need this and the behaviour is slowing down your parser,
	 * use {@link ParseTools#cut(Grammar)} to select only the longest parse.
	 *
	 * @param element the grammar to repeat
	 * @param <Result> the element type of the resulting LocatedList
	 * @return a grammar yielding a {@link LocatedList} of all the sequential parses of {@param element}. The list
	 * itself aggregates the locations of each element.
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
	 * Requests that the parsing engine memoize the provided {@param grammar}. This is useful if branch in your grammar
	 * contains a repeated prefix that is being redundantly reparsed. The first time this grammar is parsed everything
	 * will happen as usual, but if the same {@code memoize(grammar)} is encountered again in the same lexical context
	 * and the parser state is the same, the grammar will immediately yield the previous result without reparsing.
	 *
	 * <p>Note: {@param grammar} is compared to potential reparses via {@link Object#equals(Object)}, so this
	 * will only have an effect if each memoize call uses the exact same object, not a copy.</p>
	 * @param grammar the grammar to memoize (must be the same object each time)
	 * @param <Result> the result type of the memoized grammar
	 * @return a new grammar that only parses the same grammar at the same location with the same state once
	 */
	public static <Result extends SourceLocatable> Grammar<Result> memoize(Grammar<Result> grammar) {
		return new MemoizeGrammar<>(grammar);
	}

	/**
	 * Similar to {@link ParseTools#repeat(Grammar <Result>)}, but only accepting sequences of at least one element.
	 * @param element a grammar representing one element of the list
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the corresponding grammar
	 * @see ParseTools#repeat(Grammar) for caveats and notes
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

	/**
	 * Returns a grammar that parses an "empty sequence". This is not immediately useful, but is the start of
	 * this parsing library's way of combining grammars sequentially.
	 * @return a grammar that parses an empty sequence, yielding a located {@link pgo.util.EmptyHeterogenousList}
	 * @see AbstractSequenceGrammar for how to extend the sequence
	 */
	public static EmptySequenceGrammar emptySequence() { return new EmptySequenceGrammar(); }

	/**
	 * Creates a grammar that succeeds only if there does not exist a valid parse of {@param grammar} at the current
	 * location.
	 *
	 * <p>{@link ParseFailure}s caused by the execution of {@param grammar} will not propagate. Instead, if this
	 * grammar fails a {@link ParseFailure#rejectFailure(Grammar)} will be noted.</p>
	 * @param grammar the grammar to reject
	 * @return a grammar that yields the current source location if {@param grammar yields no successful parses}
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> reject(Grammar<Result> grammar){
		return new RejectGrammar<>(grammar);
	}

	/**
	 * Wraps the provided {@param grammar}, forcing it to yield exactly 0 or 1 correct parses. This is useful if
	 * a grammar is ambiguous, cannot be easily refactored to not be ambiguous and the first parse is known to always
	 * be correct if it exists. Depending on the level of ambiguity, adding this to the middle of a large grammar
	 * can save an otherwise prohibitively huge amount of unnecessary backtracking.
	 * @param grammar the grammar to wrap
	 * @param <Result> the result type of the wrapped grammar
	 * @return a grammar the yields exactly 0 or 1 results depending on whether the wrapped grammar matches anything
	 */
	public static <Result extends SourceLocatable> Grammar<Result> cut(Grammar<Result> grammar) {
		return new CutGrammar<>(grammar);
	}

	/**
	 * @return a grammar that successfully yields Void, located at the current source location.
	 */
	public static Grammar<Located<Void>> nop() {
		return matchString("");
	}

	/**
	 * Reads the provided source in its entirety by implicitly appending {@link ParseTools#matchEOF()} to the provided
	 * {@param grammar}. Otherwise semantically similar to {@link Grammar#parse(LexicalContext)}.
	 * @param ctx the lexical context in which to parse {@param grammar}
	 * @param grammar the grammar to parse
	 * @param <T> the result type of {@param grammar}
	 * @return the first parse result of {@param grammar} that covers the entire text
	 * @throws ParseFailureException if no valid parses of the entire text indicated by {@param ctx} exist, indicates
	 * the furthest {@link ParseFailure}s registered
	 */
	public static <T extends SourceLocatable> T readOrExcept(LexicalContext ctx, Grammar<T> grammar) throws ParseFailureException {
		Grammar<T> withEOF = emptySequence()
				.part(grammar)
				.drop(matchEOF())
				.map(seq -> seq.getValue().getFirst());

		return withEOF.parse(ctx);
	}

	/**
	 * Returns a grammar that only succeeds at the end of the text region indicated by the lexical context.
	 * Registers {@link ParseFailure#eofMatchFailure()} on failure.
	 * @return a grammar that yields the current source location if the lexical context points to the end of the text
	 */
	public static Grammar<Located<Void>> matchEOF() {
		return new EOFGrammar();
	}

	/**
	 * This is a utility for the common problem parsing lists with separators. Semantically similar to
	 * {@link ParseTools#repeatOneOrMore(Grammar)}, this grammar parses one or more instances of {@param element},
	 * but separated by instances of {@param sep}.
	 * @param element the grammar to repeat
	 * @param sep the separator to use
	 * @param <AST> the type of elements yielded by {@param element}
	 * @return a grammar that yields located lists of type {@param <AST>}, in order of descending length. The list
	 * includes the location(s) of {@param sep}'s results, but ignores the values yielded by {@param sep}
	 */
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
