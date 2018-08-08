package pgo.parser;

import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAString;
import pgo.util.SourceLocatable;

public final class ParseTools {
	
	private ParseTools() {}

	private static final Pattern WHITESPACE = Pattern.compile("\\s+");
	private static final Pattern TLA_IDENTIFIER = Pattern.compile("[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*");
	private static final List<String> TLA_RESERVED_WORDS = Arrays.asList(
			"ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE", "CONSTANT", "CONSTANTS", "DOMAIN",
			"ELSE", "ENABLED", "EXCEPT", "EXTENDS", "IF", "IN", "INSTANCE", "LET", "LOCAL",
			"MODULE", "OTHER", "SF_", "SUBSET", "THEN", "THEOREM", "UNCHANGED", "UNION", "VARIABLE",
			"VARIABLES", "WF_", "WITH"
	).stream().sorted(Comparator.comparing(String::length).reversed()).collect(Collectors.toList());

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

	// this matches the inside of a comment - must not contain any comment delimiters, but must be followed by either
	// one of them or the end of the input
	// DOTALL so we can munch newlines inside comments
	private static final Pattern TLA_NOT_A_COMMENT_MARKER_MULTILINE = Pattern.compile(
			".*?(?=\\(\\*|\\*\\)|$)", Pattern.DOTALL);
	private static final Pattern TLA_NOT_A_COMMENT_MARKER_LINE = Pattern.compile(
			".*?$", Pattern.MULTILINE);

	/**
	 * Returns a parse action that matches a TLA+ multi-line, nestable comment. Matches anything between a balanced
	 * pair of (* and *).
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchTLAMultilineComment(){
		return fix(self ->
				sequence(
						drop(matchString("(*")),
						drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE)),
						drop(repeat(
								sequence(
										drop(self),
										drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE))
								).map(seq -> new Located<>(seq.getLocation(), null))
						)),
						drop(matchString("*)"))
				).map(seq -> new Located<>(seq.getLocation(), null)));
	}

	/**
	 * Returns a parse action that matches a TLA+ single-line comment starting with \*
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchTLALineComment(){
		return sequence(
				drop(matchString("\\*")),
				drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_LINE))
		).map(seq -> new Located<>(seq.getLocation(), null));
	}

	/**
	 * Returns a parse action that matches either of the two styles of TLA+ comment.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchTLAComment(){
		return parseOneOf(
				matchTLAMultilineComment(),
				matchTLALineComment()
		);
	}

	/**
	 * Returns a parse action that matches and discards one or more characters of whitespace, defined as the regex
	 * class \s
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchWhitespace(){
		return matchPattern(WHITESPACE).map(res -> new Located<>(res.getLocation(), null));
	}

	/**
	 * Returns a parse action that accepts and discards any sequence of whitespace and TLA+ comments.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> skipWhitespaceAndTLAComments(){
		return repeat(parseOneOf(
				matchWhitespace(),
				matchTLAComment()
		)).map(list -> new Located<>(list.getLocation(), null));
	}

	/**
	 * Returns a parse action that matches a TLA+ identifier. This is defined to be anything matching the regex
	 * {@link ParseTools#TLA_IDENTIFIER}, except for the following cases:
	 * <ul>
	 *     <li>Anything beginning with "WF_" or "SF_"</li>
	 *     <li>Any TLA+ reserved words, defined at {@link ParseTools#TLA_RESERVED_WORDS}</li>
	 * </ul>
	 * @return the parse action
	 */
	public static Grammar<Located<String>> matchTLAIdentifier(){
		return matchPattern(TLA_IDENTIFIER)
				.map(result -> new Located<>(result.getLocation(), result.getValue().group()))
				.filter(id -> {
					String val = id.getResult().getValue();
					return !val.startsWith("WF_") && !val.startsWith("SF_") && !TLA_RESERVED_WORDS.contains(val);
				});
	}

	private static final Pattern TLA_STRING_CONTENTS = Pattern.compile("[a-zA-Z0-9~@#$%^&*_ \\-+=(){}\\[\\]<>|/,.?:;`']");

	/**
	 * Returns a parse action that will match a TLA+ string. This is defined as anything between quotation marks
	 * matching the regex {@link ParseTools#TLA_STRING_CONTENTS}, with the addition of the following escape sequences:
	 * <ul>
	 *     <li>\", for a quotation mark</li>
	 *     <li>\\, for a backslash</li>
	 *     <li>\t, for a tab character</li>
	 *     <li>\n, for a new line</li>
	 *     <li>\f, for a form feed</li>
	 *     <li>\r, for a carriage return</li>
	 * </ul>
	 * @return the parse action
	 */
	public static Grammar<PGoTLAString> matchTLAString(){
		Variable<Located<String>> nonEscape = new Variable<>("nonEscape");
		Variable<LocatedList<Located<String>>> parts = new Variable<>("parts");
		return sequence(
				drop(matchString("\"")),
				part(parts, repeat(parseOneOf(
						matchString("\\\"").map(s -> new Located<>(s.getLocation(), "\"")),
						matchString("\\\\").map(s -> new Located<>(s.getLocation(), "\\")),
						matchString("\\t").map(s -> new Located<>(s.getLocation(), "\t")),
						matchString("\\n").map(s -> new Located<>(s.getLocation(), "\n")),
						matchString("\\f").map(s -> new Located<>(s.getLocation(), "\f")),
						matchString("\\r").map(s -> new Located<>(s.getLocation(), "\r")),
						sequence(
								drop(reject(matchString("\\"))),
								part(nonEscape, matchPattern(TLA_STRING_CONTENTS)
										.map(res -> new Located<>(res.getLocation(), res.getValue().group())))
						).map(seq -> seq.get(nonEscape))
				))),
				drop(matchString("\""))
		).map(seq -> new PGoTLAString(
				seq.getLocation(),
				seq.get(parts).stream().map(p -> p.getValue()).collect(Collectors.joining())));
	}

	private static final Pattern TLA_NUMBER_INT = Pattern.compile("\\d+");
	private static final Pattern TLA_NUMBER_FLOAT = Pattern.compile("\\d*\\.\\d+");
	private static final Pattern TLA_NUMBER_BIN = Pattern.compile("\\\\[bB]([01]+)");
	private static final Pattern TLA_NUMBER_OCT = Pattern.compile("\\\\[oO]([0-7]+)");
	private static final Pattern TLA_NUMBER_HEX = Pattern.compile("\\\\[hH]([0-9a-fA-F]+)");

	/**
	 * Returns a parse action that matches any of the TLA+ number syntaxes.
	 *
	 * These are represented by the regexes:
	 * <ul>
	 *  <li>{@link ParseTools#TLA_NUMBER_INT}: integer, mapped to the number type {@link PGoTLANumber.Base#DECIMAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_FLOAT}: floating point, mapped to the number type {@link PGoTLANumber.Base#DECIMAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_BIN}: binary, mapped to the number type {@link PGoTLANumber.Base#BINARY}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_OCT}: octal, mapped to the number type {@link PGoTLANumber.Base#OCTAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_HEX}: hexadecimal, mapped to the number type {@link PGoTLANumber.Base#HEXADECIMAL}</li>
	 * </ul>
	 *
	 * In each case the representation will be stripped of any prefix, so for example the TLA+ binary notation
	 * "\b0110" will be stored as "0110".
	 *
	 * @return the parse action
	 */
	public static Grammar<PGoTLANumber> matchTLANumber(){
		return parseOneOf(
				matchPattern(TLA_NUMBER_INT).map(res ->
						new PGoTLANumber(res.getLocation(), res.getValue().group(), PGoTLANumber.Base.DECIMAL)),
				matchPattern(TLA_NUMBER_FLOAT).map(res ->
						new PGoTLANumber(res.getLocation(), res.getValue().group(), PGoTLANumber.Base.DECIMAL)),
				matchPattern(TLA_NUMBER_BIN).map(res ->
						new PGoTLANumber(res.getLocation(), res.getValue().group(1), PGoTLANumber.Base.BINARY)),
				matchPattern(TLA_NUMBER_OCT).map(res ->
						new PGoTLANumber(res.getLocation(), res.getValue().group(1), PGoTLANumber.Base.OCTAL)),
				matchPattern(TLA_NUMBER_HEX).map(res ->
						new PGoTLANumber(res.getLocation(), res.getValue().group(1), PGoTLANumber.Base.HEXADECIMAL))
		);
	}

	private static final Pattern TLA_4_DASHES_OR_MORE = Pattern.compile("----+");
	private static final Pattern TLA_4_EQUALS_OR_MORE = Pattern.compile("====+");

	// matches anything until it reaches ----+, then stops (look up reluctant quantifiers for the semantics of "*?")
	// DOTALL allows us to munch newlines
	private static final Pattern TLA_BEFORE_MODULE = Pattern.compile(".*?(?=----+)", Pattern.DOTALL);

	/**
	 * Returns a parse action that consumes any text up till the beginning of a TLA+ module, defined to be 4 or more
	 * '-' characters in a row. It does not however consume those characters, making this safe to use before
	 * {@link ParseTools#parse4DashesOrMore()}}.
	 * @return a parse action yielding the range of text skipped
	 */
	public static Grammar<Located<Void>> findModuleStart(){
		return matchPattern(TLA_BEFORE_MODULE).map(v -> new Located<>(v.getLocation(), null));
	}

	private static final Pattern TLA_AFTER_MODULE = Pattern.compile("(?:(?!----+).)*", Pattern.DOTALL);

	public static Grammar<Located<Void>> consumeAfterModuleEnd(){
		return matchPattern(TLA_AFTER_MODULE).map(v -> new Located<>(v.getLocation(), null));
	}

	/**
	 * Returns a parse actions that matches a series of 4 or more dashes (-), skipping any preceding whitespace or
	 * TLA+ comments.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parse4DashesOrMore(){
		Variable<Located<MatchResult>> res = new Variable<>("res");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(res, matchPattern(TLA_4_DASHES_OR_MORE))
		).map(seq -> new Located<>(seq.get(res).getLocation(), null));
	}

	/**
	 * Returns a parse actions that matches a series of 4 or more equals signs (=), skipping any preceding whitespace or
	 * TLA+ comments.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parse4EqualsOrMore(){
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				drop(matchPattern(TLA_4_EQUALS_OR_MORE))
		).map(seq -> new Located<>(seq.getLocation(), null));
	}

	public static final Variable<Located<Integer>> MIN_COLUMN = new Variable<>("MIN_COLUMN");

	/**
	 * Returns a parse action that behaves exactly like the provided action, but fails with
	 * {@link ParseFailure.InsufficientlyIndented} if the result is not indented at or beyond minColumn.
	 * @param action the action to perform
	 * @param minColumn the minimum column to accept
	 * @param <ParseResult> the result type of action
	 * @return the new parse action
	 */
	public static <ParseResult extends SourceLocatable> Grammar<ParseResult> checkMinColumn(Grammar<ParseResult> action, Variable<Located<Integer>> minColumn){
		if(minColumn == null) return action;
		else return action.filter(info -> info.getResult().getLocation().getStartColumn() >= info.get(minColumn).getValue());
	}

	/**
	 * Creates a parse action that accepts string t as long as it is at minColumn or more, skipping any preceding
	 * comments or whitespace.
	 * @param t the string representation that should be accepted
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parseBuiltinToken(String t, Variable<Located<Integer>> minColumn){
		Variable<Located<Void>> token = new Variable<>("token");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, checkMinColumn(matchString(t), minColumn))
		).map(seq -> new Located<>(seq.get(token).getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts the string t, skipping any preceding comments or whitespace.
	 * @param t the token to accept
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parsePlusCalToken(String t){
		Variable<Located<Void>> token = new Variable<>("token");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, matchString(t))
		).map(seq -> new Located<>(seq.get(token).getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts any of the strings in options as long as they are located at or beyond
	 * minColumn, skipping any preceding comments or whitespace.
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parseBuiltinTokenOneOf(List<String> options, Variable<Located<Integer>> minColumn){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchStringOneOf(options), minColumn))
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts any of the string in options, skipping any preceding comments or whitespace.
	 * @param options a list of token values to accept
	 * @return the parse action, yielding which token was accepted
	 */
	public static Grammar<Located<String>> parsePlusCalTokenOneOf(List<String> options){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result,matchStringOneOf(options))
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts a TLA+ identifier as long as it is located at or after minColumn, skipping
	 * any preceding whitespace. See {@link ParseTools#matchTLAIdentifier()} for a precise definition of what a TLA+
	 * identifier is.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLAIdentifier> parseIdentifier(Variable<Located<Integer>> minColumn){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAIdentifier(), minColumn))
		).map(seq -> {
			Located<String> res = seq.get(result);
			return new PGoTLAIdentifier(res.getLocation(), res.getValue());
		});
	}

	/**
	 * Creates a parse action that accepts a PlusCal identifier (identical to a TLA+ identifier, but with a more
	 * convenient return type).
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parsePlusCalIdentifier(){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, matchTLAIdentifier())
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts a TLA+ string as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLAString()} for a precise definition of what we consider a
	 * TLA+ string.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLAString> parseString(Variable<Located<Integer>> minColumn){
		Variable<PGoTLAString> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAString(), minColumn))
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts a TLA+ number as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLANumber()} for a precise definition of what we consider a
	 * TLA+ number.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLANumber> parseNumber(Variable<Located<Integer>> minColumn){
		Variable<PGoTLANumber> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLANumber(), minColumn))
		).map(seq -> seq.get(result));
	}

	/**
	 * Combines parse actions from the list of options into one single parse action. Each action will be tried in the
	 * same order as in the list, and the first successful action's result will be yielded. If none of the actions match
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
	 * If the given action succeeds, this action fails. If the given action fails, this action succeeds.
	 * @param action the parse action to be inverted
	 * @return a parse action that will successfully parse anything that is rejected by the given action
	 */
	public static <Result extends SourceLocatable> Grammar<Located<Void>> reject(Grammar<Result> action){
		return new RejectGrammar<Result>(action);
		/*Variable<Boolean> success = new Variable<>(false);
		return parseOneOf(
				action.chain(val -> {
					success.setValue(true);
					return Grammar.failure(ParseFailure.parseSuccess());
				}),
				nop().chain(v -> {
					if(success.getValue()){
						return Grammar.failure(ParseFailure.parseSuccess());
					}else{
						return Grammar.success(v);
					}
				})
		);*/
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

	public static <T extends SourceLocatable> T readOrExcept(LexicalContext ctx, Grammar<T> grammar) throws TLAParseException{
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

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseCommaList(Grammar<AST> element, Variable<Located<Integer>> minColumn){
		return parseListOf(element, parseBuiltinToken(",", minColumn));
	}

}
