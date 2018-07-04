package pgo.parser;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import pgo.lexer.TLAToken;
import pgo.lexer.TLATokenType;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.util.SourceLocatable;

public class ParseTools {
	
	private ParseTools() {}

	/**
	 * Creates a parse action that accepts a token of the specified type, with a minimum column position of minColumn.
	 * @param tokenType the expected token type
	 * @param minColumn the minimum accepted column position
	 * @return the parse action
	 */
	public static ParseAction<LocatedString> parseTokenType(TLATokenType tokenType, int minColumn){
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
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#BUILTIN} and value t
	 * @param t the string representation that should be accepted
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<LocatedString> parseBuiltinToken(String t, int minColumn){
		return parseTokenType(TLATokenType.BUILTIN, minColumn)
				.withContext(new WhileParsingBuiltinToken(t))
				.chain(s -> {
					if(s.getValue().equals(t)) {
						return ParseAction.success(s);
					}else {
						return ParseAction.failure(
								ParseFailure.unexpectedBuiltinToken(s, Collections.singletonList(t)));
					}
				});
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#BUILTIN} and a value that is
	 * one of options
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<LocatedString> parseBuiltinTokenOneOf(List<String> options, int minColumn){
		return parseTokenType(TLATokenType.BUILTIN, minColumn)
				.chain(s -> {
					if(options.contains(s.getValue())) {
						return ParseAction.success(s);
					}else {
						return ParseAction.failure(
								ParseFailure.unexpectedBuiltinToken(s, options));
					}
				});
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#IDENT}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<PGoTLAIdentifier> parseIdentifier(int minColumn){
		return parseTokenType(TLATokenType.IDENT, minColumn)
				.map(s -> new PGoTLAIdentifier(s.getLocation(), s.getValue()));
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#STRING}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<LocatedString> parseString(int minColumn){
		return parseTokenType(TLATokenType.STRING, minColumn);
	}

	/**
	 * Creates a parse action that accepts a token with type {@link pgo.lexer.TLATokenType#NUMBER}.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static ParseAction<LocatedString> parseNumber(int minColumn){
		return parseTokenType(TLATokenType.NUMBER, minColumn);
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
