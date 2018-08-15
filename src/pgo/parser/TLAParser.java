package pgo.parser;

import pgo.model.tla.*;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.function.Supplier;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static pgo.parser.ParseTools.*;

/**
 *
 *  <p>
 *  This is a backtracking LL_k parser for the TLA+ language.
 *  </p>
 *
 *  <p>
 *  It is written in order to match the grammar defined in Lamport's
 *  book Specifying Systems, Part IV as much as possible.
 *  </p>
 *
 *  <h3> Notes to the reader </h3>
 *
 *  <p>
 *  The grammar has been transcribed into parse* functions that return {@see pgo.parser.Grammar}.
 *  Start reading with {@link pgo.parser.TLAParser#parseModule}.
 *  </p>
 *
 *  <p>
 *  Endpoints that are actually called elsewhere begin with read* and perform the necessary operations to convert
 *  from returning {@link Grammar} instances to returning results and throwing errors.
 *  </p>
 *
 *  <p>
 *  Everything is defined in terms of a common vocabulary of operations, the most general of which can be found in
 *  {@link pgo.parser.ParseTools}. GoFor an overview of the basic mechanics of the system, look at
 *  {@link Grammar}.
 *  </p>
 *
 * 	<h3> Operators </h3>
 *
 * 	<p>Since TLA+ operators come in all shapes and sizes but also follow a
 * 	fairly consistent set of rules, they are treated using a set of
 * 	static arrays and maps.</p>
 *
 * 	<p>The static arrays are generally lists of operators separated by parsing
 * 	category, and the maps are used to handle operator precedence.</p>
 *
 *  <h4> *_HI_PRECEDENCE and *_LO_PRECEDENCE </h4>
 *
 * 	    <p>Since TLA+ operators have a range of possible precedences traditional
 * 	    precedence handling strategies fall short. We keep maps of the low
 * 	    and high bounds (inclusive) of each operator and instead of
 * 	    recursing over each operator in reverse precedence order we recurse
 * 	    directly over precedences themselves, matching any qualifying operators
 * 	    as we go.</p>
 *
 *  <h4> *_LEFT_ASSOCIATIVE </h4>
 *
 *  	<p>Not all operators in TLA+ support associativity. It is a parse error
 *  	to accept non-bracketed repetition of non-associative operators.</p>
 *
 *  	<p>So, we keep track of which operators are left-associative and only
 *  	accept repeated instances of those in these sets.</p>
 *
 *  <h4> Indentation sensitivity </h4>
 *
 * 		<p>TLA+ has some unusual rules surrounding chaining of the {@code /\}
 * 		and the {@code \/} operators. Specifically, in all other cases the
 * 		language can be parsed without regard for whitespace, but
 * 		when dealing with these chains it is a parse error to unindent
 * 		part of a nested expression to a column before any leading
 * 		{@code /\}  or {@code /\}.</p>
 *
 * 		<p>e.g:</p>
 *
 * 		<p>The expression:</p>
 * 	    <pre>
 * 		foo /\ x +
 * 		   1
 * 		</pre>
 *
 * 		<p>Parses as:</p>
 * 	    <pre>
 * 		(foo /\ (x+)) 1
 * 	    </pre>
 *
 *      <p>
 * 		Aside from parsing pedantry, this does affect the way the parser
 * 		finds the end of subexpressions so we must implement this.
 * 	    </p>
 *
 *      <p>
 * 		The  argument represents this constraint - if a token is found that
 * 		would otherwise match, but is at a column index lower than
 * 		, the match fails instead. This enables most of the
 * 		codebase to not have to care too much about this rule, while
 * 		consistently enforcing it.
 * 	    </p>
 *
 *      <p>
 * 		Passing {@code  = -1} is used to disable this feature for
 * 		expressions that are not on the right hand side of {@code /\} or {@code \/}.
 * 	    </p>
 *
 */
public final class TLAParser {

	private static final Pattern TLA_IDENTIFIER = Pattern.compile("[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*");
	private static final List<String> TLA_RESERVED_WORDS = Arrays.asList(
			"ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE", "CONSTANT", "CONSTANTS", "DOMAIN",
			"ELSE", "ENABLED", "EXCEPT", "EXTENDS", "IF", "IN", "INSTANCE", "LET", "LOCAL",
			"MODULE", "OTHER", "SF_", "SUBSET", "THEN", "THEOREM", "UNCHANGED", "UNION", "VARIABLE",
			"VARIABLES", "WF_", "WITH"
	).stream().sorted(Comparator.comparing(String::length).reversed()).collect(Collectors.toList());

	public static final List<String> PREFIX_OPERATORS = Arrays.asList("-",
			"~",
			"\\lnot",
			"\\neg",
			"[]",
			"<>",
			"DOMAIN",
			"ENABLED",
			"SUBSET",
			"UNCHANGED",
			"UNION")
			.stream()
			.sorted(Comparator.comparingInt(String::length).reversed())
			.collect(Collectors.toList());

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
		ReferenceGrammar<Located<Void>> recur = new ReferenceGrammar<>();
		recur.setReferencedGrammar(
				emptySequence()
						.drop(matchString("(*"))
						.drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE))
						.drop(repeat(emptySequence()
								.drop(recur)
								.drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_MULTILINE))))
						.drop(matchString("*)"))
						.map(seq -> new Located<>(seq.getLocation(), null))
		);
		return recur;
	}

	/**
	 * Returns a parse action that matches a TLA+ single-line comment starting with \*
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> matchTLALineComment(){
		return emptySequence()
				.drop(matchString("\\*"))
				.drop(matchPattern(TLA_NOT_A_COMMENT_MARKER_LINE))
				.map(seq -> new Located<>(seq.getLocation(), null));
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
	public static Grammar<TLAString> matchTLAString(){
		Variable<Located<String>> nonEscape = new Variable<>("nonEscape");
		Variable<LocatedList<Located<String>>> parts = new Variable<>("parts");
		return emptySequence()
				.drop(matchString("\""))
				.part(repeat(parseOneOf(
						matchString("\\\"").map(s -> new Located<>(s.getLocation(), "\"")),
						matchString("\\\\").map(s -> new Located<>(s.getLocation(), "\\")),
						matchString("\\t").map(s -> new Located<>(s.getLocation(), "\t")),
						matchString("\\n").map(s -> new Located<>(s.getLocation(), "\n")),
						matchString("\\f").map(s -> new Located<>(s.getLocation(), "\f")),
						matchString("\\r").map(s -> new Located<>(s.getLocation(), "\r")),
						emptySequence()
								.drop(reject(matchString("\\")))
								.part(matchPattern(TLA_STRING_CONTENTS)
										.map(res -> new Located<>(res.getLocation(), res.getValue().group())))
								.map(seq -> seq.getValue().getFirst())
				)))
				.drop(matchString("\""))
				.map(seq -> new TLAString(
						seq.getLocation(),
						seq.getValue()
								.getFirst()
								.stream()
								.map(p -> p.getValue())
								.collect(Collectors.joining())));
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
	 *  <li>{@link ParseTools#TLA_NUMBER_INT}: integer, mapped to the number type {@link TLANumber.Base#DECIMAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_FLOAT}: floating point, mapped to the number type {@link TLANumber.Base#DECIMAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_BIN}: binary, mapped to the number type {@link TLANumber.Base#BINARY}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_OCT}: octal, mapped to the number type {@link TLANumber.Base#OCTAL}</li>
	 *  <li>{@link ParseTools#TLA_NUMBER_HEX}: hexadecimal, mapped to the number type {@link TLANumber.Base#HEXADECIMAL}</li>
	 * </ul>
	 *
	 * In each case the representation will be stripped of any prefix, so for example the TLA+ binary notation
	 * "\b0110" will be stored as "0110".
	 *
	 * @return the parse action
	 */
	public static Grammar<TLANumber> matchTLANumber(){
		return parseOneOf(
				matchPattern(TLA_NUMBER_INT).map(res ->
						new TLANumber(res.getLocation(), res.getValue().group(), TLANumber.Base.DECIMAL)),
				matchPattern(TLA_NUMBER_FLOAT).map(res ->
						new TLANumber(res.getLocation(), res.getValue().group(), TLANumber.Base.DECIMAL)),
				matchPattern(TLA_NUMBER_BIN).map(res ->
						new TLANumber(res.getLocation(), res.getValue().group(1), TLANumber.Base.BINARY)),
				matchPattern(TLA_NUMBER_OCT).map(res ->
						new TLANumber(res.getLocation(), res.getValue().group(1), TLANumber.Base.OCTAL)),
				matchPattern(TLA_NUMBER_HEX).map(res ->
						new TLANumber(res.getLocation(), res.getValue().group(1), TLANumber.Base.HEXADECIMAL))
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
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchPattern(TLA_4_DASHES_OR_MORE))
				.map(seq -> new Located<>(seq.getValue().getFirst().getLocation(), null));
	}

	/**
	 * Returns a parse actions that matches a series of 4 or more equals signs (=), skipping any preceding whitespace or
	 * TLA+ comments.
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parse4EqualsOrMore(){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchPattern(TLA_4_EQUALS_OR_MORE))
				.map(seq -> new Located<>(seq.getValue().getFirst().getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts string t as long as it is at minColumn or more, skipping any preceding
	 * comments or whitespace.
	 * @param t the string representation that should be accepted
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parseTLAToken(String t){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(checkMinColumn(matchString(t)))
				.map(seq -> new Located<>(seq.getValue().getFirst().getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts any of the strings in options as long as they are located at or beyond
	 * minColumn, skipping any preceding comments or whitespace.
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parseTLATokenOneOf(List<String> options){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(checkMinColumn(matchStringOneOf(options)))
				.map(seq -> seq.getValue().getFirst());
	}

	/**
	 * Creates a parse action that accepts a TLA+ identifier as long as it is located at or after minColumn, skipping
	 * any preceding whitespace. See {@link ParseTools#matchTLAIdentifier()} for a precise definition of what a TLA+
	 * identifier is.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLAIdentifier> parseTLAIdentifier(){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(checkMinColumn(matchTLAIdentifier()))
				.map(seq -> new TLAIdentifier(
						seq.getValue().getFirst().getLocation(),
						seq.getValue().getFirst().getValue()));
	}

	/**
	 * Creates a parse action that accepts a TLA+ string as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLAString()} for a precise definition of what we consider a
	 * TLA+ string.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLAString> parseTLAString(){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(checkMinColumn(matchTLAString()))
				.map(seq -> seq.getValue().getFirst());
	}

	/**
	 * Creates a parse action that accepts a TLA+ number as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLANumber()} for a precise definition of what we consider a
	 * TLA+ number.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLANumber> parseTLANumber(){
		return emptySequence()
				.drop(skipWhitespaceAndTLAComments())
				.part(matchTLANumber())
				.map(seq -> seq.getValue().getFirst());
	}

	public static <AST extends SourceLocatable> Grammar<LocatedList<AST>> parseCommaList(Grammar<AST> element){
		return parseListOf(element, parseTLAToken(","));
	}
	
	public static Map<String, Integer> PREFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
	static {
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("-", 12);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("~", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("\\lnot", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("\\neg", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("[]", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("<>", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("DOMAIN", 9);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("ENABLED", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("SUBSET", 8);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("UNCHANGED", 4);
		PREFIX_OPERATORS_LOW_PRECEDENCE.put("UNION", 8);
	}
	
	public static Map<String, Integer> PREFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
	static {
		PREFIX_OPERATORS_HI_PRECEDENCE.put("-", 12);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("~", 4);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("\\lnot", 4);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("\\neg", 4);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("[]", 15);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("<>", 15);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("DOMAIN", 9);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("ENABLED", 15);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("SUBSET", 8);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("UNCHANGED", 15);
		PREFIX_OPERATORS_HI_PRECEDENCE.put("UNION", 8);
	}
	
	public static final List<String> INFIX_OPERATORS = Arrays.asList(// infix operators (non-alpha)
			"!!",
			"#",
			"##",
			"$",
			"$$",
			"%",
			"%%",
			"&",
			"&&",
			"(+)",
			"(-)",
			"(.)",
			"(/)",
			"(\\X)",
			"*",
			"**",
			"+",
			"++",
			"-",
			"-+->",
			"--",
			"-|",
			"..",
			"...",
			"/",
			"//",
			"/=",
			"/\\",
			"::=",
			":=",
			":>",
			"<",
			"<:",
			"<=",
			"<=>",
			"=",
			"=<",
			"=>",
			"=|",
			">",
			">=",
			"?",
			"??",
			"@@",
			"\\",
			"\\/",
			"^",
			"^^",
			"|",
			"|-",
			"|=",
			"||",
			"~>",
			".",
			// infix operators (alpha)
			"\\approx",
			"\\geq",
			"\\oslash",
			"\\sqsupseteq",
			"\\asymp",
			"\\gg",
			"\\otimes",
			"\\star",
			"\\bigcirc",
			"\\in",
			"\\notin",
			"\\prec",
			"\\subset",
			"\\bullet",
			"\\intersect",
			"\\preceq",
			"\\subseteq",
			"\\cap",
			"\\land",
			"\\propto",
			"\\succ",
			"\\cdot",
			"\\leq",
			"\\sim",
			"\\succeq",
			"\\circ",
			"\\ll",
			"\\simeq",
			"\\supset",
			"\\cong",
			"\\lor",
			"\\sqcap",
			"\\supseteq",
			"\\cup",
			"\\o",
			"\\sqcup",
			"\\union",
			"\\div",
			"\\odot",
			"\\sqsubset",
			"\\uplus",
			"\\doteq",
			"\\ominus",
			"\\sqsubseteq",
			"\\wr",
			"\\equiv",
			"\\oplus",
			"\\sqsupset")
			.stream()
			.sorted(Comparator.comparingInt(String::length).reversed())
			.collect(Collectors.toList());
	
	public static Map<String, Integer> INFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
	static {
		// infix operators (non-alpha)
		INFIX_OPERATORS_LOW_PRECEDENCE.put("!!", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("#", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("##", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("$", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("$$", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("%", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("%%", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("&", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("&&", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("(+)", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("(-)", 11);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("(.)", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("(/)", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("(\\X)", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("*", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("**", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("+", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("++", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("-", 11);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("-+->", 2);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("--", 11);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("-|", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("..", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("...", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("/", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("//", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("/=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("/\\", 3);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("::=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put(":=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put(":>", 7);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("<", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("<:", 7);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("<=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("<=>", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("=<", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("=>", 1);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("=|", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put(">", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put(">=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("?", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("??", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("@@", 6);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\", 8);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\/", 3);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("^", 14);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("^^", 14);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("|", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("|-", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("|=", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("||", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("~>", 2);
		INFIX_OPERATORS_LOW_PRECEDENCE.put(".", 17);
		// infix operators (alpha)
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\approx", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\geq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\oslash", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqsupseteq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\asymp", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\gg", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\otimes", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\star", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\bigcirc", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\in", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\notin", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\prec", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\subset", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\bullet", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\intersect", 8);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\preceq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\subseteq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\cap", 8);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\land", 3);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\propto", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\succ", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\cdot", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\leq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sim", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\succeq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\circ", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\ll", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\simeq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\supset", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\cong", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\lor", 3);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqcap", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\supseteq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\cup", 8);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\o", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqcup", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\union", 8);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\div", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\odot", 13);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqsubset", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\uplus", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\doteq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\ominus", 11);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqsubseteq", 5);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\wr", 9);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\equiv", 2);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\oplus", 10);
		INFIX_OPERATORS_LOW_PRECEDENCE.put("\\sqsupset", 5);
	}
	
	public static Map<String, Integer> INFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
	static {
		// infix operators (non-alpha)
		INFIX_OPERATORS_HI_PRECEDENCE.put("!!", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("#", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("##", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("$", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("$$", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("%", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("%%", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("&", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("&&", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("(+)", 10);
		INFIX_OPERATORS_HI_PRECEDENCE.put("(-)", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("(.)", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("(/)", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("(\\X)", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("*", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("**", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("+", 10);
		INFIX_OPERATORS_HI_PRECEDENCE.put("++", 10);
		INFIX_OPERATORS_HI_PRECEDENCE.put("-", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("-+->", 2);
		INFIX_OPERATORS_HI_PRECEDENCE.put("--", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("-|", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("..", 9);
		INFIX_OPERATORS_HI_PRECEDENCE.put("...", 9);
		INFIX_OPERATORS_HI_PRECEDENCE.put("/", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("//", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("/=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("/\\", 3);
		INFIX_OPERATORS_HI_PRECEDENCE.put("::=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put(":=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put(":>", 7);
		INFIX_OPERATORS_HI_PRECEDENCE.put("<", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("<:", 7);
		INFIX_OPERATORS_HI_PRECEDENCE.put("<=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("<=>", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("=<", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("=>", 1);
		INFIX_OPERATORS_HI_PRECEDENCE.put("=|", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put(">", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put(">=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("?", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("??", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("@@", 6);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\", 8);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\/", 3);
		INFIX_OPERATORS_HI_PRECEDENCE.put("^", 14);
		INFIX_OPERATORS_HI_PRECEDENCE.put("^^", 14);
		INFIX_OPERATORS_HI_PRECEDENCE.put("|", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("|-", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("|=", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("||", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("~>", 2);
		INFIX_OPERATORS_HI_PRECEDENCE.put(".", 17);
		// infix operators (alpha)
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\approx", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\geq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\oslash", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqsupseteq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\asymp", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\gg", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\otimes", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\star", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\bigcirc", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\in", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\notin", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\prec", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\subset", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\bullet", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\intersect", 8);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\preceq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\subseteq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\cap", 8);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\land", 3);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\propto", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\succ", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\cdot", 14);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\leq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sim", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\succeq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\circ", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\ll", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\simeq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\supset", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\cong", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\lor", 3);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqcap", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\supseteq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\cup", 8);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\o", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqcup", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\union", 8);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\div", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\odot", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqsubset", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\uplus", 13);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\doteq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\ominus", 11);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqsubseteq", 5);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\wr", 14);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\equiv", 2);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\oplus", 10);
		INFIX_OPERATORS_HI_PRECEDENCE.put("\\sqsupset", 5);
	}
	
	public static Set<String> INFIX_OPERATORS_LEFT_ASSOCIATIVE = new HashSet<>();
	static {
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\/");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("/\\");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\cdot");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("@@");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\cap");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\cup");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("##");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("$");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("$$");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("??");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\sqcap");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\sqcup");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\uplus");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\oplus");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("++");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("+");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("%%");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("|");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("||");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\ominus");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("-");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("--");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("&");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("&&");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\odot");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\otimes");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("*");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("**");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\circ");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\bullet");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\o");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add("\\star");
		INFIX_OPERATORS_LEFT_ASSOCIATIVE.add(".");
	}
	
	public static final List<String> POSTFIX_OPERATORS = Arrays.asList("^+",
			"^*",
			"^#",
			"'")
			.stream()
			.sorted(Comparator.comparingInt(String::length).reversed())
			.collect(Collectors.toList());

	public static Map<String, Integer> POSTFIX_OPERATORS_PRECEDENCE = new HashMap<>();
	static {
		POSTFIX_OPERATORS_PRECEDENCE.put("^+", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^*", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^#", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("'", 15);
	}
	
	private TLAParser(){}

	public static final Map<Integer, ReferenceGrammar<TLAExpression>> OPERATORS_BY_PRECEDENCE = new HashMap<>(17);
	static {
		for(int i = 1; i <= 18; ++i){
			OPERATORS_BY_PRECEDENCE.put(i, new ReferenceGrammar<>());
		}
	}
	public static final ReferenceGrammar<TLAExpression> EXPRESSION_NO_OPERATORS = new ReferenceGrammar<>();
	public static final ReferenceGrammar<TLAExpression> EXPRESSION = OPERATORS_BY_PRECEDENCE.get(1);
	
	static Grammar<TLAIdentifierOrTuple> parseIdentifierTuple(){
		return emptySequence()
				.drop(parseTLAToken("<<"))
				.part(parseOneOf(
						parseCommaList(parseTLAIdentifier()),
						nop().map(v -> new LocatedList<TLAIdentifier>(v.getLocation(), Collections.emptyList()))
				))
				.drop(parseTLAToken(">>"))
				.map(seq -> TLAIdentifierOrTuple.Tuple(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAIdentifierOrTuple> parseIdentifierOrTuple() {
		return parseOneOf(
				parseTLAIdentifier()
						.map(TLAIdentifierOrTuple::Identifier),
				parseIdentifierTuple());
	}
	
	static Grammar<TLAQuantifierBound> parseQuantifierBound(){
		return parseOneOf(
				emptySequence()
						.part(parseIdentifierTuple().map(t -> new LocatedList<>(t.getLocation(), t.getTuple())))
						.drop(parseTLAToken("\\in"))
						.part(EXPRESSION)
						.map(seq -> new TLAQuantifierBound(
								seq.getLocation(),
								TLAQuantifierBound.Type.TUPLE,
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst())),
				emptySequence()
						.part(parseCommaList(parseTLAIdentifier()))
						.drop(parseTLAToken("\\in"))
						.part(EXPRESSION)
						.map(seq -> new TLAQuantifierBound(
								seq.getLocation(),
								TLAQuantifierBound.Type.IDS,
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst()))
		);
	}
	
	static final Grammar<LocatedList<TLAGeneralIdentifierPart>> INSTANCE_PREFIX =
			repeat(
				emptySequence()
						.part(parseTLAIdentifier())
						.part(parseOneOf(
								emptySequence()
										.drop(parseTLAToken("("))
										.part(parseCommaList(EXPRESSION))
										.drop(parseTLAToken(")"))
										.map(seq -> seq.getValue().getFirst()),
								nop().map(v -> new LocatedList<TLAExpression>(v.getLocation(), Collections.emptyList()))
						))
						.drop(parseTLAToken("!"))
						.map(seq -> new TLAGeneralIdentifierPart(
								seq.getLocation(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst()))
		);
	
	static Grammar<TLAExpression> parseTupleExpression(){
		return emptySequence()
				.drop(parseTLAToken("<<"))
				.part(parseOneOf(
						parseCommaList(EXPRESSION),
						nop().map(v -> new LocatedList<TLAExpression>(v.getLocation(), Collections.emptyList()))
				))
				.drop(parseTLAToken(">>"))
				.map(seq -> new TLATuple(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseRequiredActionExpression(){
		return emptySequence()
				.drop(parseTLAToken("<<"))
				.part(EXPRESSION)
				.drop(parseTLAToken(">>_"))
				.part(EXPRESSION)
				.map(seq -> new TLARequiredAction(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseOperatorCall(){
		return emptySequence()
				.part(INSTANCE_PREFIX)
				.part(parseTLAIdentifier())
				.drop(parseTLAToken("("))
				.part(parseCommaList(EXPRESSION))
				.drop(parseTLAToken(")"))
				.map(seq -> new TLAOperatorCall(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getRest().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseGeneralIdentifier(){
		return emptySequence()
				.part(INSTANCE_PREFIX)
				.part(parseTLAIdentifier())
				.map(seq -> new TLAGeneralIdentifier(
						seq.getLocation(),
						seq.getValue().getFirst(),
						seq.getValue().getRest().getFirst()));
	}

	static Grammar<TLAExpression> parseConjunct() {
		return parseConjunctOrDisjunct("/\\");
	}

	private static final class ConjunctDisjunctPart {
		private Located<Void> symLocation;
		private TLAExpression expr;

		public ConjunctDisjunctPart(Located<Void> symLocation, TLAExpression expr) {
			this.symLocation = symLocation;
			this.expr = expr;
		}

		public Located<Void> getSymLocation() {
			return symLocation;
		}

		public TLAExpression getExpr() { return expr; }
	}
	
	static Grammar<TLAExpression> parseConjunctOrDisjunct(String which){
		return emptySequence()
				.part(parseTLAToken(which))
				.dependentPart(EXPRESSION, info -> new VariableMap()
						.put(MIN_COLUMN,info.getResult().getValue().getFirst().getLocation().getStartColumn()+1))
				.dependentPart(
						repeat(
								emptySequence()
										.part(parseTLAToken(which))
										.part(EXPRESSION)
						),
						info -> new VariableMap()
								.put(MIN_COLUMN, info.getResult().getValue().getFirst().getLocation().getStartColumn()))
				.map(seq -> {
					if(seq.getValue().getFirst().isEmpty()) {
						return seq.getValue().getRest().getFirst();
					}else{
						Located<Void> firstSym = seq.getValue().getRest().getRest().getFirst();
						TLAExpression lhs = seq.getValue().getRest().getFirst();
						LocatedList<
								Located<AbstractHeterogenousList<
										TLAExpression, AbstractHeterogenousList<
										Located<Void>, EmptyHeterogenousList>>>> rest = seq.getValue().getFirst();
						lhs = new TLABinOp(
								lhs.getLocation()
										.combine(firstSym.getLocation())
										.combine(rest.get(0).getLocation()),
								new TLASymbol(firstSym.getLocation(), which),
								Collections.emptyList(),
								lhs,
								seq.getValue().getFirst().get(0).getValue().getFirst());
						for(Located<AbstractHeterogenousList<
								TLAExpression, AbstractHeterogenousList<
								Located<Void>, EmptyHeterogenousList>>> part : rest.subList(1, rest.size())) {
							lhs = new TLABinOp(
									lhs.getLocation().combine(part.getLocation()),
									new TLASymbol(part.getValue().getRest().getFirst().getLocation(), which),
									Collections.emptyList(),
									lhs,
									part.getValue().getFirst());
						}
						return lhs;
					}
				});
	}
	
	static Grammar<TLAExpression> parseDisjunct(){
		return parseConjunctOrDisjunct("\\/");
	}
	
	static Grammar<TLAExpression> parseIfExpression(){
		return emptySequence()
				.drop(parseTLAToken("IF"))
				.part(EXPRESSION)
				.drop(parseTLAToken("THEN"))
				.part(EXPRESSION)
				.drop(parseTLAToken("ELSE"))
				.part(EXPRESSION)
				.map(seq -> new TLAIf(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getFirst(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	public static Grammar<TLAExpression> parseCaseExpression(){
		return emptySequence()
				.drop(parseTLAToken("CASE"))
				.part(emptySequence()
						.part(EXPRESSION)
						.drop(parseTLAToken("->"))
						.part(EXPRESSION)
						.map(seq -> new TLACaseArm(
								seq.getLocation(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst())))
				.part(repeat(
						emptySequence()
								.drop(parseTLAToken("[]"))
								.part(EXPRESSION)
								.drop(parseTLAToken("->"))
								.part(EXPRESSION)
								.map(seq -> new TLACaseArm(
										seq.getLocation(),
										seq.getValue().getRest().getFirst(),
										seq.getValue().getFirst()))
				))
				.part(parseOneOf(
						emptySequence()
								.drop(parseTLAToken("[]"))
								.drop(parseTLAToken("OTHER"))
								.drop(parseTLAToken("->"))
								.part(EXPRESSION)
								.map(seq -> new Located<>(seq.getLocation(), seq.getValue().getFirst())),
						nop().map(v -> new Located<TLAExpression>(v.getLocation(), null))
				))
				.map(seq -> {
					LocatedList<TLACaseArm> arms = new LocatedList<>(SourceLocation.unknown(), new ArrayList<>());
					arms.add(seq.getValue().getRest().getRest().getFirst());
					arms.addLocation(seq.getValue().getRest().getRest().getFirst().getLocation());
					arms.addAll(seq.getValue().getRest().getFirst());
					arms.addLocation(seq.getValue().getRest().getFirst().getLocation());
					return new TLACase(seq.getLocation(), arms, seq.getValue().getFirst().getValue());
				});
	}
	
	static Grammar<TLAExpression> parseFunctionExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(parseCommaList(parseQuantifierBound()))
				.drop(parseTLAToken("|->"))
				.part(EXPRESSION)
				.drop(parseTLAToken("]"))
				.map(seq -> new TLAFunction(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseRecordSetExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(parseCommaList(
						emptySequence()
								.part(parseTLAIdentifier())
								.drop(parseTLAToken(":"))
								.part(EXPRESSION)
								.map(seq -> new TLARecordSet.Field(
										seq.getLocation(),
										seq.getValue().getRest().getFirst(),
										seq.getValue().getFirst()))
				))
				.drop(parseTLAToken("]"))
				.map(seq -> new TLARecordSet(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseRecordConstructorExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(parseCommaList(
						emptySequence()
								.part(parseTLAIdentifier())
								.drop(parseTLAToken("|->"))
								.part(EXPRESSION)
								.map(seq -> new TLARecordConstructor.Field(
										seq.getLocation(),
										seq.getValue().getRest().getFirst(),
										seq.getValue().getFirst()))
				))
				.drop(parseTLAToken("]"))
				.map(seq -> new TLARecordConstructor(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseFunctionSetExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(EXPRESSION)
				.drop(parseTLAToken("->"))
				.part(EXPRESSION)
				.drop(parseTLAToken("]"))
				.map(seq -> new TLAFunctionSet(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseMaybeActionExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(EXPRESSION)
				.drop(parseTLAToken("]_"))
				.part(EXPRESSION)
				.map(seq -> new TLAMaybeAction(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseFunctionSubstitutionExpression(){
		return emptySequence()
				.drop(parseTLAToken("["))
				.part(EXPRESSION)
				.drop(parseTLAToken("EXCEPT"))
				.part(parseCommaList(
						emptySequence()
								.drop(parseTLAToken("!"))
								.part(repeatOneOrMore(
										parseOneOf(
												emptySequence()
														.drop(parseTLAToken("."))
														.part(parseTLAIdentifier())
														.map(seq -> new TLASubstitutionKey(
																seq.getLocation(),
																Collections.singletonList(
																		new TLAString(
																				seq.getValue().getFirst().getLocation(),
																				seq.getValue().getFirst().getId())))),
												emptySequence()
														.drop(parseTLAToken("["))
														.part(parseCommaList(EXPRESSION))
														.drop(parseTLAToken("]"))
														.map(seq -> new TLASubstitutionKey(
																seq.getLocation(),
																seq.getValue().getFirst()))
										)
								))
								.drop(parseTLAToken("="))
								.part(EXPRESSION)
								.map(seq -> new TLAFunctionSubstitutionPair(
										seq.getLocation(),
										seq.getValue().getRest().getFirst(),
										seq.getValue().getFirst()))
				))
				.drop(parseTLAToken("]"))
				.map(seq -> new TLAFunctionSubstitution(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseGroupExpression(){
		return emptySequence()
				.drop(parseTLAToken("("))
				.part(EXPRESSION)
				.drop(parseTLAToken(")"))
				.map(seq -> seq.getValue().getFirst());
	}
	
	static Grammar<TLAExpression> parseQuantifiedExistentialExpression(){
		return emptySequence()
				.drop(parseTLAToken("\\E"))
				.part(parseCommaList(parseQuantifierBound()))
				.drop(parseTLAToken(":"))
				.part(EXPRESSION)
				.map(seq -> new TLAQuantifiedExistential(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}

	static Grammar<TLAExpression> parseQuantifiedUniversalExpression(){
		return emptySequence()
				.drop(parseTLAToken("\\A"))
				.part(parseCommaList(parseQuantifierBound()))
				.drop(parseTLAToken(":"))
				.part(EXPRESSION)
				.map(seq -> new TLAQuantifiedUniversal(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseUnquantifiedExistentialExpression(){
		return emptySequence()
				.drop(parseOneOf(parseTLAToken("\\EE"), parseTLAToken("\\E")))
				.part(parseCommaList(parseTLAIdentifier()))
				.drop(parseTLAToken(":"))
				.part(EXPRESSION)
				.map(seq -> new TLAExistential(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseUnquantifiedUniversalExpression(){
		return emptySequence()
				.drop(parseOneOf(parseTLAToken("\\AA"), parseTLAToken("\\A")))
				.part(parseCommaList(parseTLAIdentifier()))
				.drop(parseTLAToken(":"))
				.part(EXPRESSION)
				.map(seq -> new TLAUniversal(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseSetConstructorExpression(){
		return emptySequence()
				.drop(parseTLAToken("{"))
				.part(parseOneOf(
						parseCommaList(EXPRESSION),
						nop().map(v -> new LocatedList<TLAExpression>(v.getLocation(), Collections.emptyList()))
				))
				.drop(parseTLAToken("}"))
				.map(seq -> new TLASetConstructor(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseSetRefinementExpression(){
		return emptySequence()
				.drop(parseTLAToken("{"))
				.part(parseIdentifierOrTuple())
				.drop(parseTLAToken("\\in"))
				.part(EXPRESSION)
				.drop(parseTLAToken(":"))
				.part(EXPRESSION)
				.drop(parseTLAToken("}"))
				.map(seq -> new TLASetRefinement(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getFirst(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseSetComprehensionExpression(){
		return emptySequence()
				.drop(parseTLAToken("{"))
				.part(EXPRESSION)
				.drop(parseTLAToken(":"))
				.part(parseCommaList(parseQuantifierBound()))
				.drop(parseTLAToken("}"))
				.map(seq -> new TLASetComprehension(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}
	
	static Grammar<TLAExpression> parseLetExpression(){
		return emptySequence()
				.drop(parseTLAToken("LET"))
				.part(repeatOneOrMore(
						parseOneOf(
								parseOperatorDefinition(false),
								parseFunctionDefinition(false),
								parseModuleDefinition(false)
						)
				))
				.drop(parseTLAToken("IN"))
				.part(EXPRESSION)
				.map(seq -> new TLALet(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}

	static Grammar<TLAExpression> parseFairnessConstraint(){
		return emptySequence()
				.part(parseOneOf(
						parseTLAToken("WF_").map(v -> new Located<>(v.getLocation(), TLAFairness.Type.WEAK)),
						parseTLAToken("SF_").map(v -> new Located<>(v.getLocation(), TLAFairness.Type.STRONG))
				))
				.part(EXPRESSION)
				.drop(parseTLAToken("("))
				.part(EXPRESSION)
				.drop(parseTLAToken(")"))
				.map(seq -> new TLAFairness(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getFirst().getValue(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}

	private static final class InfixOperatorPart {

		private LocatedList<TLAGeneralIdentifierPart> prefix;
		private Located<Void> symLocation;
		private TLAExpression rhs;
		private Located<InfixOperatorPart> next;

		public InfixOperatorPart(LocatedList<TLAGeneralIdentifierPart> prefix, Located<Void> symLocation,
								 TLAExpression rhs, Located<InfixOperatorPart> next) {
			this.prefix = prefix;
			this.symLocation = symLocation;
			this.rhs = rhs;
			this.next = next;
		}

		public void setNext(Located<InfixOperatorPart> next) {
			this.next = next;
		}

		public LocatedList<TLAGeneralIdentifierPart> getPrefix() {
			return prefix;
		}

		public Located<Void> getSymLocation() {
			return symLocation;
		}

		public TLAExpression getRhs() {
			return rhs;
		}

		public TLAExpression applyLhs(SourceLocation loc, TLAExpression lhs, String opName) {
			if(next.getValue() != null) {
				lhs = next.getValue().applyLhs(next.getLocation(), lhs, opName);
			}
			return new TLABinOp(
					lhs.getLocation().combine(loc),
					new TLASymbol(symLocation.getLocation(), opName),
					prefix, lhs, rhs);
		}
	}

	private static Grammar<TLAExpression> parsePrefixOperator(int precedence) {
		List<String> operatorOptions = PREFIX_OPERATORS
				.stream()
				.filter(op ->
						/*precedence >= PREFIX_OPERATORS_LOW_PRECEDENCE.get(op)
								&& */precedence <= PREFIX_OPERATORS_HI_PRECEDENCE.get(op))
				.collect(Collectors.toList());

		if(operatorOptions.isEmpty()) return parseOneOf(Collections.emptyList());

		ReferenceGrammar<TLAExpression> self = new ReferenceGrammar<>();

		self.setReferencedGrammar(
				emptySequence()
						.part(INSTANCE_PREFIX)
						.part(parseOneOf(
								operatorOptions
										.stream()
										.map(operator -> emptySequence()
												.part(parseTLAToken(operator)
														.map(v -> new TLASymbol(v.getLocation(), operator)))
												.part(parseOneOf(
														self,
														OPERATORS_BY_PRECEDENCE
																.get(PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)
												)))
										.collect(Collectors.toList())
						))
						.map(seq -> new TLAUnary(
								seq.getLocation(),
								seq.getValue().getFirst().getValue().getRest().getFirst(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst().getValue().getFirst())));

		return self;
	}

	private static TLAExpression buildPostfixExpression(TLAExpression lhs, LocatedList<Located<PostfixOperatorPart>> parts) {
		for(Located<PostfixOperatorPart> part : parts) {
			if(part.getValue().isFunctionCall()) {
				lhs = new TLAFunctionCall(
						lhs.getLocation().combine(part.getLocation()),
						lhs,
						part.getValue().getFunctionArguments());
			}else{
				lhs = new TLAUnary(
						lhs.getLocation().combine(part.getLocation()),
						new TLASymbol(part.getValue().getOp().getLocation(), part.getValue().getOp().getValue()),
						part.getValue().getPrefix(),
						lhs);
			}
		}
		return lhs;
	}

	private static Grammar<TLAExpression> parseExpressionFromPrecedence(int precedence) {

		List<String> relevantPostfixOperators = POSTFIX_OPERATORS
				.stream()
				.filter(operator -> POSTFIX_OPERATORS_PRECEDENCE.get(operator) >= precedence)
				.collect(Collectors.toList());

		List<Grammar<? extends Located<PostfixOperatorPart>>> postfixOperatorPartOptions = new ArrayList<>();
		if(precedence <= 16) {
			postfixOperatorPartOptions.add(
					emptySequence()
							.drop(parseTLAToken("["))
							.part(parseCommaList(EXPRESSION))
							.drop(parseTLAToken("]"))
							.map(seq -> new Located<>(
									seq.getLocation(),
									new PostfixOperatorPart(
											null,
											null,
											seq.getValue().getFirst(),
											true)))
			);
		}
		postfixOperatorPartOptions.add(
				emptySequence()
						.part(INSTANCE_PREFIX)
						.part(parseTLATokenOneOf(relevantPostfixOperators))
						.map(seq -> new Located<>(
								seq.getLocation(),
								new PostfixOperatorPart(
										seq.getValue().getRest().getFirst(),
										seq.getValue().getFirst(),
										null,
										false))
						)
		);

		return parseOneOf(
				// infix operators
				parseOneOf(
						INFIX_OPERATORS.stream()
								.filter(operator ->
										INFIX_OPERATORS_LOW_PRECEDENCE.get(operator) <= precedence
												&& INFIX_OPERATORS_HI_PRECEDENCE.get(operator) >= precedence)
								.map(operator ->
										emptySequence()
												.part(OPERATORS_BY_PRECEDENCE.get(precedence+1))
												.part(INFIX_OPERATORS_LEFT_ASSOCIATIVE.contains(operator) ?
														repeatOneOrMore(
																emptySequence()
																		.part(INSTANCE_PREFIX)
																		.part(parseInfixOperator(operator))
																		.part(OPERATORS_BY_PRECEDENCE
																				.get(INFIX_OPERATORS_HI_PRECEDENCE
																						.get(operator)+1))
														) : emptySequence()
																.part(INSTANCE_PREFIX)
																.part(parseInfixOperator(operator))
																.part(OPERATORS_BY_PRECEDENCE
																		.get(INFIX_OPERATORS_HI_PRECEDENCE
																				.get(operator)+1))
																.map(seq -> new LocatedList<>(
																		seq.getLocation(),
																		Collections.singletonList(seq)))
												)
												.map(seq -> {
													TLAExpression lhs = seq.getValue().getRest().getFirst();
													for(Located<
															? extends AbstractHeterogenousList<
																	TLAExpression,
																	? extends AbstractHeterogenousList<
																			Located<Void>,
																			? extends AbstractHeterogenousList<
																					LocatedList<TLAGeneralIdentifierPart>,
																					?>>>> e :
															seq.getValue().getFirst()) {
														lhs = new TLABinOp(
																lhs.getLocation().combine(e.getLocation()),
																new TLASymbol(
																		e.getValue().getRest().getFirst().getLocation(),
																		operator),
																e.getValue().getRest().getRest().getFirst(),
																lhs,
																e.getValue().getFirst());
													}
													return lhs;
												}))
								.collect(Collectors.toList())
				),
				// postfix operators
				emptySequence()
						.part(OPERATORS_BY_PRECEDENCE.get(precedence+1))
						.part(repeatOneOrMore(parseOneOf(postfixOperatorPartOptions)))
						.map(seq -> buildPostfixExpression(
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst())),
				// actually nothing, just go to the next precedence level
				OPERATORS_BY_PRECEDENCE.get(precedence+1)
		);
	}

	private static Grammar<Located<Void>> parseInfixOperator(String operator) {
		List<String> supersets = new ArrayList<>();
		for(String possibleSuperset : INFIX_OPERATORS) {
			if(possibleSuperset.length() > operator.length() && possibleSuperset.startsWith(operator)) {
				supersets.add(possibleSuperset);
			}
		}

		if(supersets.isEmpty()) return parseTLAToken(operator);

		return emptySequence()
				.drop(reject(
						parseOneOf(
								supersets.stream()
										.map(sup -> parseTLAToken(sup))
										.collect(Collectors.toList()))))
				.part(parseTLAToken(operator))
				.map(seq -> seq.getValue().getFirst());
	}

	static {
		for(int i = 1; i <= 17; ++i){
			int j = i;
			OPERATORS_BY_PRECEDENCE.get(i).setReferencedGrammar(
					parseOneOf(
							parseExpressionFromPrecedence(i),
							parsePrefixOperator(i)
					)
			);
		}
		OPERATORS_BY_PRECEDENCE.get(18).setReferencedGrammar(EXPRESSION_NO_OPERATORS);
	}
	static {
		EXPRESSION_NO_OPERATORS.setReferencedGrammar(
				parseOneOf(
						parseTLANumber(),
						parseTLAString(),
						parseTLATokenOneOf(
								Arrays.asList("TRUE", "FALSE"))
								.map(b -> new TLABool(b.getLocation(), b.getValue().equals("TRUE"))),

						parseGroupExpression(),
						parseTupleExpression(),

						parseRequiredActionExpression(),

						parseOperatorCall(),
						// looks like an operator call but is different (WF_.*|SF_.*)
						parseFairnessConstraint(),

						parseConjunct(),
						parseDisjunct(),

						parseIfExpression(),

						parseGeneralIdentifier(),

						parseLetExpression(),

						parseCaseExpression(),
						// starting with [
						parseFunctionExpression(),
						parseRecordSetExpression(),
						parseRecordConstructorExpression(),
						parseFunctionSetExpression(),
						parseMaybeActionExpression(),
						parseFunctionSubstitutionExpression(),
						// starting with \E, \EE, \A, \AA
						parseQuantifiedExistentialExpression(),
						parseQuantifiedUniversalExpression(),
						parseUnquantifiedExistentialExpression(),
						parseUnquantifiedUniversalExpression(),
						//starting with {
						parseSetConstructorExpression(),
						parseSetRefinementExpression(),
						parseSetComprehensionExpression()
				));
	}

	private static final class PostfixOperatorPart {
		private LocatedList<TLAGeneralIdentifierPart> prefix;
		private Located<String> op;
		private LocatedList<TLAExpression> functionArguments;
		private boolean functionCall;

		public PostfixOperatorPart(LocatedList<TLAGeneralIdentifierPart> prefix, Located<String> op,
								   LocatedList<TLAExpression> functionArguments, boolean functionCall) {
			this.prefix = prefix;
			this.op = op;
			this.functionArguments = functionArguments;
			this.functionCall = functionCall;
		}

		public LocatedList<TLAGeneralIdentifierPart> getPrefix() {
			return prefix;
		}

		public Located<String> getOp() {
			return op;
		}

		public LocatedList<TLAExpression> getFunctionArguments() {
			return functionArguments;
		}

		public boolean isFunctionCall() {
			return functionCall;
		}
	}


	public static Grammar<TLAExpression> parseExpression(){
		return emptySequence()
				.dependentPart(EXPRESSION, ignore -> new VariableMap().put(MIN_COLUMN, -1))
				.map(seq -> seq.getValue().getFirst());
	}
	
	static Grammar<TLAOpDecl> parseOpDecl(){
		return parseOneOf(
				emptySequence()
						.part(parseTLAIdentifier())
						.drop(parseTLAToken("("))
						.part(parseCommaList(parseTLAToken("_")))
						.drop(parseTLAToken(")"))
						.map(seq -> TLAOpDecl.Named(
								seq.getLocation(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst().size())),
				parseTLAIdentifier().map(id -> TLAOpDecl.Id(id.getLocation(), id)),
				emptySequence()
						.part(parseTLATokenOneOf(PREFIX_OPERATORS))
						.drop(parseTLAToken("_"))
						.map(seq -> {
							Located<String> op = seq.getValue().getFirst();
							// operator - is the only operator that is both unary and binary, and can be defined as
							// both simultaneously. We special-case the unary version by renaming it.
							String value = op.getValue().equals("-") ? "-_" : op.getValue();
							return TLAOpDecl.Prefix(seq.getLocation(), new TLAIdentifier(op.getLocation(), value));
						}),
				emptySequence()
						.drop(parseTLAToken("_"))
						.part(parseTLATokenOneOf(INFIX_OPERATORS))
						.drop(parseTLAToken("_"))
						.map(seq -> {
							Located<String> op = seq.getValue().getFirst();
							return TLAOpDecl.Infix(
									seq.getLocation(),
									new TLAIdentifier(op.getLocation(), op.getValue()));
						}),
				emptySequence()
						.drop(parseTLAToken("_"))
						.part(parseTLATokenOneOf(POSTFIX_OPERATORS))
						.map(seq -> {
							Located<String> op = seq.getValue().getFirst();
							return TLAOpDecl.Postfix(
									seq.getLocation(),
									new TLAIdentifier(op.getLocation(), op.getValue()));
						})
		);
	}
	
	static Grammar<TLAUnit> parseOperatorDefinition(boolean isLocal){
		return parseOneOf(
				emptySequence()
						.part(parseTLATokenOneOf(PREFIX_OPERATORS))
						.part(parseTLAIdentifier())
						.drop(parseTLAToken("=="))
						.part(EXPRESSION)
						.map(seq -> {
							Located<String> op = seq.getValue().getRest().getRest().getFirst();
							// operator - is the only operator that is both unary and binary, and can
							// be defined as both simultaneously. We special-case the unary version by
							// renaming it.
							String value = op.getValue().equals("-") ? "-_" : op.getValue();
							return new TLAOperatorDefinition(
									seq.getLocation(),
									new TLAIdentifier(op.getLocation(), value),
									Collections.singletonList(TLAOpDecl.Id(
											op.getLocation(), seq.getValue().getRest().getFirst())),
									seq.getValue().getFirst(),
									isLocal);
						}),
				emptySequence()
						.part(parseTLAIdentifier())
						.part(parseTLATokenOneOf(INFIX_OPERATORS))
						.part(parseTLAIdentifier())
						.drop(parseTLAToken("=="))
						.part(EXPRESSION)
						.map(seq -> {
							TLAIdentifier lhs = seq.getValue().getRest().getRest().getRest().getFirst();
							Located<String> op = seq.getValue().getRest().getRest().getFirst();
							TLAIdentifier rhs = seq.getValue().getRest().getFirst();
							return new TLAOperatorDefinition(
									seq.getLocation(),
									new TLAIdentifier(op.getLocation(), op.getValue()),
									Arrays.asList(
											TLAOpDecl.Id(lhs.getLocation(), lhs),
											TLAOpDecl.Id(rhs.getLocation(), rhs)),
									seq.getValue().getFirst(),
									isLocal);
						}),
				emptySequence()
						.part(parseTLAIdentifier())
						.part(parseTLATokenOneOf(POSTFIX_OPERATORS))
						.drop(parseTLAToken("=="))
						.part(EXPRESSION)
						.map(seq -> {
							TLAIdentifier lhs = seq.getValue().getRest().getRest().getFirst();
							Located<String> op = seq.getValue().getRest().getFirst();
							return new TLAOperatorDefinition(
									seq.getLocation(),
									new TLAIdentifier(op.getLocation(), op.getValue()),
									Collections.singletonList(TLAOpDecl.Id(lhs.getLocation(), lhs)),
									seq.getValue().getFirst(),
									isLocal);
						}),
				emptySequence()
						.part(parseTLAIdentifier())
						.part(parseOneOf(
								emptySequence()
										.drop(parseTLAToken("("))
										.part(parseCommaList(parseOpDecl()))
										.drop(parseTLAToken(")"))
										.map(seq -> seq.getValue().getFirst()),
								nop().map(v -> new LocatedList<TLAOpDecl>(v.getLocation(), Collections.emptyList()))
						))
						.drop(parseTLAToken("=="))
						.part(EXPRESSION)
						.map(seq -> new TLAOperatorDefinition(
								seq.getLocation(),
								seq.getValue().getRest().getRest().getFirst(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst(), isLocal))
		);
	}
	
	static Grammar<TLAUnit> parseFunctionDefinition(boolean isLocal){
		return emptySequence()
				.part(parseTLAIdentifier())
				.drop(parseTLAToken("["))
				.part(parseCommaList(parseQuantifierBound()))
				.drop(parseTLAToken("]"))
				.drop(parseTLAToken("=="))
				.part(EXPRESSION)
				.map(seq -> new TLAFunctionDefinition(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getFirst(),
						new TLAFunction(
								seq.getLocation(),
								seq.getValue().getRest().getFirst(),
								seq.getValue().getFirst()),
						isLocal));
	}
	
	static Grammar<TLAInstance> parseInstance(boolean isLocal){
		return emptySequence()
				.drop(parseTLAToken("INSTANCE"))
				.part(parseTLAIdentifier())
				.part(parseOneOf(
						emptySequence()
								.drop(parseTLAToken("WITH"))
								.part(parseCommaList(
										emptySequence()
												.part(parseOneOf(
														parseTLAIdentifier(),
														parseTLATokenOneOf(PREFIX_OPERATORS).map(v ->
																new TLAIdentifier(v.getLocation(), v.getValue())),
														parseTLATokenOneOf(INFIX_OPERATORS).map(op ->
																new TLAIdentifier(op.getLocation(), op.getValue())),
														parseTLATokenOneOf(POSTFIX_OPERATORS).map(op ->
																new TLAIdentifier(op.getLocation(), op.getValue()))
												))
												.drop(parseTLAToken("<-"))
												.part(EXPRESSION)
												.map(seq -> new TLAInstance.Remapping(
														seq.getLocation(),
														seq.getValue().getRest().getFirst(),
														seq.getValue().getFirst()))

								))
								.map(seq -> seq.getValue().getFirst()),
						nop().map(v -> new LocatedList<TLAInstance.Remapping>(v.getLocation(), Collections.emptyList()))
				))
				.map(seq -> new TLAInstance(
						seq.getLocation(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst(), isLocal));

	}
	
	static Grammar<TLAUnit> parseModuleDefinition(boolean isLocal){
		return emptySequence()
				.part(parseTLAIdentifier())
				.part(parseOneOf(
						emptySequence()
								.drop(parseTLAToken("("))
								.part(parseCommaList(parseOpDecl()))
								.drop(parseTLAToken(")"))
								.map(seq -> seq.getValue().getFirst()),
						nop().map(v -> new LocatedList<TLAOpDecl>(v.getLocation(), Collections.emptyList()))
				))
				.drop(parseTLAToken("=="))
				.part(parseInstance(isLocal))
				.map(seq -> new TLAModuleDefinition(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getFirst(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst(),
						isLocal));
	}
	
	static Grammar<LocatedList<TLAIdentifier>> parseExtends(){
		return emptySequence()
				.drop(parseTLAToken("EXTENDS"))
				.part(parseCommaList(parseTLAIdentifier()))
				.map(seq -> seq.getValue().getFirst());
	}
	
	static Grammar<TLAUnit> parseVariableDeclaration() {
		return emptySequence()
				.drop(parseTLATokenOneOf(Arrays.asList("VARIABLES", "VARIABLE")))
				.part(parseCommaList(parseTLAIdentifier()))
				.map(seq -> new TLAVariableDeclaration(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAUnit> parseConstantDeclaration(){
		return emptySequence()
				.drop(parseTLATokenOneOf(Arrays.asList("CONSTANTS", "CONSTANT")))
				.part(parseCommaList(parseOpDecl()))
				.map(seq -> new TLAConstantDeclaration(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAUnit> parseAssumption(){
		return emptySequence()
				.drop(parseTLATokenOneOf(Arrays.asList("ASSUME", "ASSUMPTION", "AXIOM")))
				.part(EXPRESSION)
				.map(seq -> new TLAAssumption(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAUnit> parseTheorem(){
		return emptySequence()
				.drop(parseTLAToken("THEOREM"))
				.part(EXPRESSION)
				.map(seq -> new TLATheorem(seq.getLocation(), seq.getValue().getFirst()));
	}
	
	static Grammar<TLAUnit> parseUnit(){
		return emptySequence()
				.drop(parseOneOf(parse4DashesOrMore(), nop()))
				.part(parseOneOf(
						// all LOCAL declarations
						emptySequence()
								.drop(parseTLAToken("LOCAL"))
								.part(parseOneOf(
										parseInstance(true),
										parseModuleDefinition(true),
										parseFunctionDefinition(true),
										parseOperatorDefinition(true)
								))
								.map(seq -> seq.getValue().getFirst()),
						// all other declarations
						parseOneOf(
								parseInstance(false),
								parseModuleDefinition(false),
								parseFunctionDefinition(false),
								parseOperatorDefinition(false),
								parseVariableDeclaration(),
								parseConstantDeclaration(),
								parseAssumption(),
								parseTheorem(),
								MODULE)
				)).map(seq -> seq.getValue().getFirst());
	}

	static final Pattern TLA_BEGIN_TRANSLATION = Pattern.compile("\\\\\\*+\\s+BEGIN TRANSLATION\\s*$", Pattern.MULTILINE);
	static final Pattern TLA_END_TRANSLATION = Pattern.compile("\\\\\\*+\\s+END TRANSLATION\\s*$", Pattern.MULTILINE);

	static Grammar<Located<Void>> parseStartTranslation(){
		return emptySequence()
				.drop(repeat(parseOneOf(
						matchWhitespace(),
						matchTLAMultilineComment()
				)))
				.part(matchPattern(TLA_BEGIN_TRANSLATION))
				.map(seq -> new Located<>(seq.getValue().getFirst().getLocation(), null));
	}

	static Grammar<Located<Void>> parseEndTranslation(){
		return emptySequence()
				.drop(repeat(parseOneOf(
						matchWhitespace(),
						matchTLAMultilineComment()
				)))
				.part(matchPattern(TLA_END_TRANSLATION))
				.map(seq -> new Located<>(seq.getValue().getFirst().getLocation(), null));
	}
	
	static Grammar<TLAModule> parseModule(){
		return emptySequence()
				.drop(findModuleStart())
				.drop(parse4DashesOrMore())
				.drop(parseTLAToken("MODULE"))
				.part(parseTLAIdentifier())
				.drop(parse4DashesOrMore())
				.part(parseOneOf(
						parseExtends(),
						nop().map(v -> new LocatedList<TLAIdentifier>(v.getLocation(), Collections.emptyList()))
				))
				.part(repeat(
						emptySequence()
								.drop(reject(parseStartTranslation()))
								.part(UNIT)
								.map(seq -> seq.getValue().getFirst())
				))
				.part(
						emptySequence()
								.drop(parseStartTranslation())
								.part(repeat(
										emptySequence()
												.drop(reject(parseEndTranslation()))
												.part(UNIT)
												.map(seq -> seq.getValue().getFirst())
								))
								.drop(parseEndTranslation())
								.map(seq -> seq.getValue().getFirst())
				)
				.part(repeat(UNIT))
				.drop(parse4EqualsOrMore())
				.drop(consumeAfterModuleEnd())
				.map(seq -> new TLAModule(
						seq.getLocation(),
						seq.getValue().getRest().getRest().getRest().getRest().getFirst(),
						seq.getValue().getRest().getRest().getRest().getFirst(),
						seq.getValue().getRest().getRest().getFirst(),
						seq.getValue().getRest().getFirst(),
						seq.getValue().getFirst()));
	}

	private static final ReferenceGrammar<TLAUnit> UNIT = new ReferenceGrammar<>();
	private static final ReferenceGrammar<TLAModule> MODULE = new ReferenceGrammar<>();
	static {
		UNIT.setReferencedGrammar(parseUnit());
		MODULE.setReferencedGrammar(parseModule());
	}
	
	// external interfaces
	
	public static TLAExpression readExpression(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, parseExpression());
	}
	
	public static List<TLAUnit> readUnits(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, repeat(UNIT));
	}
	
	public static TLAUnit readUnit(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, UNIT);
	}

	public static List<TLAModule> readModules(LexicalContext ctx) throws ParseFailureException {
		return readOrExcept(ctx, repeatOneOrMore(MODULE));
	}
}