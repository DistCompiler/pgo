package pgo.parser;

import java.util.*;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import pgo.lexer.TLAToken;
import pgo.lexer.TLATokenType;
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

	public static ParseAction<Located<Void>> matchString(String token){
		return ctx -> {
			if(ctx.isEOF()){
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}
			SourceLocation loc = ctx.matchString(token);
			if(loc != null){
				return ParseResult.success(new Located<>(loc, null));
			}else{
				return ParseResult.failure(ParseFailure.stringMatchFailure(ctx.getSourceLocation(), token));
			}
		};
	}

	public static ParseAction<Located<String>> matchStringOneOf(List<String> options){
		return ctx -> {
			if(ctx.isEOF()){
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}
			for(String option : options){
				SourceLocation loc = ctx.matchString(option);
				if(loc != null){
					return ParseResult.success(new Located<>(loc, option));
				}
			}
			return ParseResult.failure(
					ParseFailure.noBranchesMatched(
							options
									.stream()
									.map(option -> ParseFailure.stringMatchFailure(ctx.getSourceLocation(), option))
									.collect(Collectors.toList())));
		};
	}

	public static ParseAction<Located<MatchResult>> matchPattern(Pattern pattern){
		return ctx -> {
			if(ctx.isEOF()){
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}
			Located<MatchResult> res = ctx.matchPattern(pattern);
			if(res != null){
				return ParseResult.success(res);
			}else{
				return ParseResult.failure(ParseFailure.patternMatchFailure(ctx.getSourceLocation(), pattern));
			}
		};
	}

	public static ParseAction<Located<String>> matchCharacters(int count){
		return ctx -> {
			if(ctx.isEOF()){
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}
			Located<String> result = ctx.matchCharacters(count);
			if(result != null){
				return ParseResult.success(result);
			}else{
				return ParseResult.failure(ParseFailure.unexpectedEOF()); // FIXME
			}
		};
	}

	// this matches the inside of a comment - must not contain any comment delimiters, but must be followed by either
	// one of them or the end of the input
	// DOTALL so we can munch newlines inside comments
	private static final Pattern TLA_NOT_A_COMMENT_MARKER_MULTILINE = Pattern.compile(
			".*?(?=\\(\\*|\\*\\)|$)", Pattern.DOTALL);
	private static final Pattern TLA_NOT_A_COMMENT_MARKER_LINE = Pattern.compile(
			".*?$", Pattern.MULTILINE);

	public static ParseAction<Located<Void>> matchTLAMultilineComment(){
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

	public static ParseAction<Located<Void>> matchTLALineComment(){
		return sequence(
				drop(matchString("\\*")),
				drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_LINE))
		).map(seq -> new Located<>(seq.getLocation(), null));
	}

	public static ParseAction<Located<Void>> matchTLAComment(){
		return parseOneOf(
				matchTLAMultilineComment(),
				matchTLALineComment()
		);
	}

	public static ParseAction<Located<Void>> matchWhitespace(){
		return matchPattern(WHITESPACE).map(res -> new Located<>(res.getLocation(), null));
	}

	public static ParseAction<Located<Void>> skipWhitespaceAndTLAComments(){
		return repeat(parseOneOf(
				matchWhitespace(),
				matchTLAComment()
		)).map(list -> new Located<>(list.getLocation(), null));
	}

	public static ParseAction<Located<String>> matchTLAIdentifier(){
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

	public static ParseAction<PGoTLAString> matchTLAString(){
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

	public static ParseAction<PGoTLANumber> matchTLANumber(){
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

	public static ParseAction<Located<Void>> findModuleStart(){
		return matchPattern(TLA_BEFORE_MODULE).map(v -> new Located<>(v.getLocation(), null));
	}

	public static ParseAction<Located<Void>> parse4DashesOrMore(){
		Mutator<Located<MatchResult>> res = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(res, matchPattern(TLA_4_DASHES_OR_MORE))
		).map(seq -> new Located<>(res.getValue().getLocation(), null));
	}

	public static ParseAction<Located<Void>> parse4EqualsOrMore(){
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				drop(matchPattern(TLA_4_EQUALS_OR_MORE))
		).map(seq -> new Located<>(seq.getLocation(), null));
	}

	public static <ParseResult extends SourceLocatable> ParseAction<ParseResult> checkMinColumn(ParseAction<ParseResult> action, int minColumn){
		return action.chain(result -> {
			if(result.getLocation().getStartColumn() < minColumn){
				return ParseAction.failure(ParseFailure.insufficientlyIndented(minColumn, result.getLocation()));
			}else{
				return ParseAction.success(result);
			}
		});
	}

	/**
	 * Creates a parse action that accepts a token of the specified type, with a minimum column position of minColumn.
	 * @param tokenType the expected token type
	 * @param minColumn the minimum accepted column position
	 * @return the parse action
	 */
	/*public static ParseAction<LocatedString> parseTokenType(TLATokenType tokenType, int minColumn){
		return ctx -> {
			TLAToken tok = ctx.readToken();
			if(tok == null) {
				return ParseResult.failure(ParseFailure.unexpectedEOF());
			}else if(tok.getLocation().getStartColumn() < minColumn) {
				return ParseResult.failure(ParseFailure.insufficientlyIndented(minColumn, tok.getLocation()));
			}else if(tok.getType() != tokenType) {
				return ParseResult.failure(ParseFailure.unexpectedTokenType(tok.getType(), tokenType, tok.getLocation()));
			}else {
				return ParseResult.success(new LocatedString(tok.getValue(), tok.getLocation()));
			}
		};
	}*/

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#BUILTIN} and value t
	 * @param t the string representation that should be accepted
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<Located<Void>> parseBuiltinToken(String t, int minColumn){
		Mutator<Located<Void>> token = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, checkMinColumn(matchString(t), minColumn))
		).map(seq -> new Located<>(token.getValue().getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#BUILTIN} and a value that is
	 * one of options
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<Located<String>> parseBuiltinTokenOneOf(List<String> options, int minColumn){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchStringOneOf(options), minColumn))
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#IDENT}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<PGoTLAIdentifier> parseIdentifier(int minColumn){
		Mutator<Located<String>> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAIdentifier(), minColumn))
		).map(seq -> new PGoTLAIdentifier(result.getValue().getLocation(), result.getValue().getValue()));
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#STRING}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<PGoTLAString> parseString(int minColumn){
		Mutator<PGoTLAString> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAString(), minColumn))
		).map(seq -> result.getValue());
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#NUMBER}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<PGoTLANumber> parseNumber(int minColumn){
		Mutator<PGoTLANumber> result = new Mutator<>();
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLANumber(), minColumn))
		).map(seq -> result.getValue());
	}

	/**
	 * Combines parse actions from the list of options into one single parse action. Each action will be tried in the
	 * same order as in the list, and the first successful action's result will be yielded. If none of the actions match
	 * the entire set of parse failures will be yielded.
	 * @param options a list of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	public static <Result> ParseAction<Result> parseOneOf(List<ParseAction<? extends Result>> options){
		return new ParseActionOneOf<Result>(options);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#parseOneOf(List<ParseAction<? extends Result>)}.
	 * @param options an array of parse actions to try
	 * @param <Result> the common result type of all the parse actions
	 * @return the combined parse action
	 */
	@SafeVarargs
	public static <Result> ParseAction<Result> parseOneOf(ParseAction<? extends Result>... options){
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
	public static <Result extends SourceLocatable> ParseAction<LocatedList<Result>> repeat(ParseAction<Result> element){
		return new ParseActionRepeated<Result>(element);
	}

	/**
	 * Similar to {@link pgo.parser.ParseTools#repeat(ParseAction<Result>)}, but only accepting sequences of at least one element.
	 * @param element a parse action representing one element of the list
	 * @param <Result> the element type of the resulting LocatedList
	 * @return the parse action
	 */
	public static <Result extends SourceLocatable> ParseAction<LocatedList<Result>> repeatOneOrMore(ParseAction<Result> element){
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
	 * is expressed as a series of {@link pgo.parser.ParseActionSequence.Part} objects. Here is some example code:</p>
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
	 * {@link pgo.parser.ParseActionSequence} yields a {@link pgo.parser.ParseActionSequenceResult} which holds metadata
	 * for the entire parse including dropped elements, currently only the entire source location.
	 * </p>
	 *
	 * @param parts a list of parts of the sequence to parse
	 * @see pgo.parser.ParseTools#sequence(ParseActionSequence.Part...)
	 * @return a parse action that will yield parse metadata for the entire sequence, use mutators and
	 * 		{@link pgo.parser.ParseAction#map} to transform this result into the desired data structure as described
	 * 		above.
	 */
	public static ParseAction<ParseActionSequenceResult> sequence(List<ParseActionSequence.Part> parts){
		return new ParseActionSequence(parts);
	}

	/**
	 * The varargs version of {@link pgo.parser.ParseTools#sequence(List<ParseActionSequence.Part)}
	 * @param parts an array of sequence parts, representing the sequence the parse action should recognise
	 * @return the parse action
	 */
	public static ParseAction<ParseActionSequenceResult> sequence(ParseActionSequence.Part... parts){
		return sequence(Arrays.asList(parts));
	}

	/**
	 * Creates a {@link pgo.parser.ParseActionSequence.Part}. This represents a part of the sequence that is of interest.
	 * @param mutator the mutator in which to store the result of parsing this part of the sequence
	 * @param action the parse action to execute as this part of the sequence
	 * @param <Result> the type of the parse action's result (also the type of the mutator's value)
	 * @return a part of a parse action sequence
	 */
	public static <Result extends SourceLocatable> ParseActionSequence.Part part(Mutator<Result> mutator, ParseAction<Result> action){
		return ParseActionSequence.part(mutator, action);
	}

	/**
	 * Creates a part of a {@link pgo.parser.ParseActionSequence}. This represents a part of a sequence that is not of
	 * interest but still part of the grammar like punctuation, brackets, etc...
	 *
	 * Executes the parse action then discards the result.
	 *
	 * @param action the parse action to execute
	 * @param <Result> the type of the discarded result
	 * @return a part of a parse action sequence
	 */
	public static <Result extends SourceLocatable> ParseActionSequence.Part drop(ParseAction<Result> action){
		return ParseActionSequence.part(new DropMutator<Result>(), action);
	}

	/**
	 * Creates a parse action that inverts the result of the given parse action.
	 * If the given action succeeds, this action fails. If the given action fails, this action succeeds.
	 * @param action the parse action to be inverted
	 * @return a parse action that will successfully parse anything that is rejected by the given action
	 */
	public static ParseAction<Located<Void>> reject(ParseAction<?> action){
		return ctx -> {
			ParseContext.Mark mark = ctx.mark();
			ParseResult<?> result = action.perform(ctx);
			if(result.isSuccess()){
				return ParseResult.failure(ParseFailure.parseSuccess()); // FIXME
			}else{
				ctx.restore(mark);
				return ParseResult.success(null);
			}
		};
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
	 * @return a parse action that successfully parses no tokens and yields null.
	 */
	public static ParseAction<Void> nop(){
		return ParseAction.success(null);
	}

}
