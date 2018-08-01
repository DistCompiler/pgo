package pgo.parser;

import java.util.*;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAString;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

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
		return resultMutator -> Collections.singletonList(new StringParseAction(token, resultMutator));
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
		return resultMutator -> Collections.singletonList(new PatternParseAction(pattern, resultMutator));
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
		return sequence(
				drop(matchString("(*")),
				drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE)),
				drop(repeat(
						sequence(
								drop(nop().chain(v -> matchTLAMultilineComment())),
								drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE))
						).map(seq -> new Located<>(seq.getLocation(), null))
				)),
				drop(matchString("*)"))
		).map(seq -> new Located<>(seq.getLocation(), null));
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
		Mutator<Located<MatchResult>> result = new Mutator<>();
		return sequence(
				drop(reject(matchStringOneOf(Arrays.asList("WF_", "SF_")))),
				drop(reject(matchStringOneOf(TLA_RESERVED_WORDS))),
				part(result, matchPattern(TLA_IDENTIFIER))
		).map(seq -> {
			String value = result.getValue().getValue().group();
			SourceLocation location = result.getValue().getLocation();
			return new Located<>(location, value);
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
		Mutator<Located<String>> nonEscape = new Mutator<>();
		Mutator<LocatedList<Located<String>>> parts = new Mutator<>();
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
						).map(seq -> nonEscape.getValue())
				))),
				drop(matchString("\""))
		).map(seq -> new PGoTLAString(
				seq.getLocation(),
				parts.getValue().stream().map(p -> p.getValue()).collect(Collectors.joining())));
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

	/**
	 * Returns a parse actions that matches a series of 4 or more dashes (-), skipping any preceding whitespace or
	 * TLA+ comments.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parse4DashesOrMore(){
		Mutator<Located<MatchResult>> res = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(res, matchPattern(TLA_4_DASHES_OR_MORE))
		).map(seq -> new Located<>(res.getValue().getLocation(), null));
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

	/**
	 * Returns a parse action that behaves exactly like the provided action, but fails with
	 * {@link ParseFailure.InsufficientlyIndented} if the result is not indented at or beyond minColumn.
	 * @param action the action to perform
	 * @param minColumn the minimum column to accept
	 * @param <ParseResult> the result type of action
	 * @return the new parse action
	 */
	public static <ParseResult extends SourceLocatable> Grammar<ParseResult> checkMinColumn(Grammar<ParseResult> action, int minColumn){
		return action.chain(result -> {
			if(result.getLocation().getStartColumn() < minColumn){
				return Grammar.failure(ParseFailure.insufficientlyIndented(minColumn, result.getLocation()));
			}else{
				return Grammar.success(result);
			}
		});
	}

	/**
	 * Creates a parse action that accepts string t as long as it is at minColumn or more, skipping any preceding
	 * comments or whitespace.
	 * @param t the string representation that should be accepted
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parseBuiltinToken(String t, int minColumn){
		Mutator<Located<Void>> token = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, checkMinColumn(matchString(t), minColumn))
		).map(seq -> new Located<>(token.getValue().getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts the string t, skipping any preceding comments or whitespace.
	 * @param t the token to accept
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parsePlusCalToken(String t){
		Mutator<Located<Void>> token = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, matchString(t))
		).map(seq -> new Located<>(token.getValue().getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts any of the strings in options as long as they are located at or beyond
	 * minColumn, skipping any preceding comments or whitespace.
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parseBuiltinTokenOneOf(List<String> options, int minColumn){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchStringOneOf(options), minColumn))
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts any of the string in options, skipping any preceding comments or whitespace.
	 * @param options a list of token values to accept
	 * @return the parse action, yielding which token was accepted
	 */
	public static Grammar<Located<String>> parsePlusCalTokenOneOf(List<String> options){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result,matchStringOneOf(options))
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts a TLA+ identifier as long as it is located at or after minColumn, skipping
	 * any preceding whitespace. See {@link ParseTools#matchTLAIdentifier()} for a precise definition of what a TLA+
	 * identifier is.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLAIdentifier> parseIdentifier(int minColumn){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAIdentifier(), minColumn))
		).map(seq -> new PGoTLAIdentifier(result.getValue().getLocation(), result.getValue().getValue()));
	}

	/**
	 * Creates a parse action that accepts a PlusCal identifier (identical to a TLA+ identifier, but with a more
	 * convenient return type).
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parsePlusCalIdentifier(){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, matchTLAIdentifier())
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts a TLA+ string as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLAString()} for a precise definition of what we consider a
	 * TLA+ string.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLAString> parseString(int minColumn){
		Mutator<PGoTLAString> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAString(), minColumn))
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts a TLA+ number as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLANumber()} for a precise definition of what we consider a
	 * TLA+ number.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<PGoTLANumber> parseNumber(int minColumn){
		Mutator<PGoTLANumber> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLANumber(), minColumn))
		).map(seq -> result.getValue());
	}

	private static Stream<ParseAction> flattenActionTrie(ActionTrie trie) {
		Stream.Builder<ParseAction> builder = Stream.builder();
		for(ParseAction action : trie.getPrefix()) {
			builder.add(action);
		}
		List<List<ParseAction>> options = new ArrayList<>();
		for(ActionTrie t : trie.getSuccessors()) {
			options.add(flattenActionTrie(t).collect(Collectors.toList()));
		}
		if(!options.isEmpty()) {
			builder.add(new BranchParseAction(options));
		}
		return builder.build();
	}

	/**
	 * Combines parse actions from the list of options into one single parse action. Each action will be tried in the
	 * same order as in the list, and the first successful action's result will be yielded. If none of the actions match
	 * the entire set of parse failures will be yielded.
	 * @param options a list of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	public static <Result> Grammar<Result> parseOneOf(List<Grammar<? extends Result>> options){
		/*return resultMutator -> {
			ActionTrie trie = new ActionTrie(options.get(0).getActions(resultMutator).collect(Collectors.toList()));
			Iterator<Grammar<? extends Result>> optiontIt = options.listIterator(1);
			while(optiontIt.hasNext()) {
				List<ParseAction> option = optiontIt.next().getActions(resultMutator).collect(Collectors.toList());
				trie.addActionSequence(option);
			}
			return flattenActionTrie(trie);
		};*/
		return resultMutator -> {
			List<List<ParseAction>> compiledOptions = new ArrayList<>(options.size());
			for(Grammar<? extends Result> option : options) {
				compiledOptions.add(option.getActions(resultMutator));
			}
			return Collections.singletonList(new BranchParseAction(compiledOptions));
		};
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#parseOneOf(List< Grammar <? extends Result>)}.
	 * @param options an array of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	public static <Result> Grammar<Result> parseOneOf(Grammar<? extends Result>... options){
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
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeat(Grammar<Result> element){
		LocatedList<Result> theList = new LocatedList<>(SourceLocation.unknown(), new ArrayList<>());

		Mutator<Grammar.Operation<Result, Located<Void>>> opSelf = new Mutator<>();
		Grammar.Operation<Result, Located<Void>> op = e -> {
			theList.addLocation(e.getLocation());
			theList.add(e);
			return parseOneOf(element.chain(opSelf.getValue()), nop());
		};
		opSelf.setValue(op);

		return parseOneOf(element.chain(op), nop().map(v -> {
			theList.addLocation(v.getLocation());
			return v;
		})).map(v -> theList);
	}

	/**
	 * Similar to {@link pgo.parser.ParseTools#repeat(Grammar <Result>)}, but only accepting sequences of at least one element.
	 * @param element a parse action representing one element of the list
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the parse action
	 */
	public static <Result extends SourceLocatable> Grammar<LocatedList<Result>> repeatOneOrMore(Grammar<Result> element){
		Mutator<Result> first = new Mutator<>();
		Mutator<LocatedList<Result>> rest = new Mutator<>();
		return sequence(
				part(first, element),
				part(rest, repeat(element))
				).map(seqResult -> {
					rest.getValue().addLocation(seqResult.getLocation());
					rest.getValue().add(0, first.getValue());
					return rest.getValue();
				});
	}

	/**
	 * <p>A tool for expressing a sequence of consecutive parse actions.</p>
	 *
	 * <p>In order to work better within the context of Java, we do some unusual things here. The sequence of actions
	 * is expressed as a series of {@link GrammarSequencePart} objects. Here is some example code:</p>
	 *
	 * <pre>{@code
	 * Mutator<Result> mut = new Mutator<>();
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
	 * {@link pgo.parser.Mutator} mut.
	 * </p>
	 *
	 * <p>
	 * Since for accurate source location tracking we want to know the location of everything we parsed,
	 * the sequence yields a {@link pgo.parser.ParseActionSequenceResult} which holds metadata
	 * for the entire parse including dropped elements, currently only the entire source location.
	 * </p>
	 *
	 * @param parts a list of parts of the sequence to parse
	 * @see pgo.parser.ParseTools#sequence(GrammarSequencePart...)
	 * @return a parse action that will yield parse metadata for the entire sequence, use mutators and
	 * 		{@link Grammar#map} to transform this result into the desired data structure as described
	 * 		above.
	 */
	public static Grammar<ParseActionSequenceResult> sequence(List<GrammarSequencePart> parts){
		return resultMutator -> {
			List<ParseAction> actions = new ArrayList<>();
			for(GrammarSequencePart part : parts) {
				actions.addAll(part.getActions());
			}
			actions.add(new ExecutorParseAction(() -> {
				SourceLocation loc = SourceLocation.unknown();
				for(GrammarSequencePart part : parts) {
					loc = loc.combine(part.getLocation());
				}
				resultMutator.setValue(new ParseActionSequenceResult(loc));
				return Collections.emptyList();
			}));
			return actions;
		};
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#sequence(List< GrammarSequencePart)}
	 * @param parts an array of sequence parts, representing the sequence the parse action should recognise
	 * @return the parse action
	 */
	public static Grammar<ParseActionSequenceResult> sequence(GrammarSequencePart... parts){
		return sequence(Arrays.asList(parts));
	}

	/**
	 * Creates a {@link GrammarSequencePart}. This represents a part of the sequence that is of interest.
	 * @param mutator the mutator in which to store the result of parsing this part of the sequence
	 * @param action the parse action to execute as this part of the sequence
	 * @param <Result> the type of the parse action's result (also the type of the mutator's value)
	 * @return a part of a parse action sequence
	 */
	public static <Result extends SourceLocatable> GrammarSequencePart part(Mutator<Result> mutator, Grammar<Result> action){
		return new GrammarSequencePart(mutator, action);
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
	public static <Result extends SourceLocatable> GrammarSequencePart drop(Grammar<Result> action){
		return new GrammarSequencePart(new Mutator<>(), action);
	}

	/**
	 * Creates a parse action that inverts the result of the given parse action.
	 * If the given action succeeds, this action fails. If the given action fails, this action succeeds.
	 * @param action the parse action to be inverted
	 * @return a parse action that will successfully parse anything that is rejected by the given action
	 */
	public static <Result> Grammar<Located<Void>> reject(Grammar<Result> action){
		Mutator<Boolean> success = new Mutator<>(false);
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
		);
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
		return resultMutator -> Collections.singletonList(new QueryPositionParseAction(resultMutator));
	}

	public static <T> T readOrExcept(LexicalContext ctx, Grammar<T> grammar) throws TLAParseException{
		return grammar.parse(ctx);
	}

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseListOf(Grammar<AST> element, Grammar<? extends SourceLocatable> sep){
		return element.chain(first ->
				repeat(nop().chain(v -> {
					Mutator<AST> ast = new Mutator<>();
					return sequence(
							drop(sep),
							part(ast, element)
					).map(seqResult -> ast.getValue());
				})).map((LocatedList<AST> list) -> {
					list.add(0, first);
					list.addLocation(first.getLocation());
					return list;
				})
		);
	}

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseCommaList(Grammar<AST> element, int minColumn){
		return parseListOf(element, parseBuiltinToken(",", minColumn));
	}

}
