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
		).map(seq -> new TLAString(
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

	/**
	 * Creates a parse action that accepts string t as long as it is at minColumn or more, skipping any preceding
	 * comments or whitespace.
	 * @param t the string representation that should be accepted
	 * @return the parse action
	 */
	public static Grammar<Located<Void>> parseTLAToken(String t){
		Variable<Located<Void>> token = new Variable<>("token");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(token, checkMinColumn(matchString(t)))
		).map(seq -> new Located<>(seq.get(token).getLocation(), null));
	}

	/**
	 * Creates a parse action that accepts any of the strings in options as long as they are located at or beyond
	 * minColumn, skipping any preceding comments or whitespace.
	 * @param options a list of acceptable token values
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<Located<String>> parseTLATokenOneOf(List<String> options){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchStringOneOf(options)))
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts a TLA+ identifier as long as it is located at or after minColumn, skipping
	 * any preceding whitespace. See {@link ParseTools#matchTLAIdentifier()} for a precise definition of what a TLA+
	 * identifier is.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLAIdentifier> parseTLAIdentifier(){
		Variable<Located<String>> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAIdentifier()))
		).map(seq -> {
			Located<String> res = seq.get(result);
			return new TLAIdentifier(res.getLocation(), res.getValue());
		});
	}

	/**
	 * Creates a parse action that accepts a TLA+ string as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLAString()} for a precise definition of what we consider a
	 * TLA+ string.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLAString> parseTLAString(){
		Variable<TLAString> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLAString()))
		).map(seq -> seq.get(result));
	}

	/**
	 * Creates a parse action that accepts a TLA+ number as long as it is located after minColumn, skipping any
	 * preceding whitespace. See {@link ParseTools#matchTLANumber()} for a precise definition of what we consider a
	 * TLA+ number.
	 * @param minColumn the minimum column at which to accept a token
	 * @return the parse action
	 */
	public static Grammar<TLANumber> parseTLANumber(){
		Variable<TLANumber> result = new Variable<>("result");
		return sequence(
				drop(skipWhitespaceAndTLAComments()),
				part(result, checkMinColumn(matchTLANumber()))
		).map(seq -> seq.get(result));
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
	
	static Grammar<TLAIdentifierOrTuple> parseIdentifierTuple(){
		Variable<LocatedList<TLAIdentifier>> ids = new Variable<>("ids");
		return sequence(
				drop(parseTLAToken("<<")),
				part(ids, parseOneOf(
						parseCommaList(parseTLAIdentifier()),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseTLAToken(">>"))
		).map(seqResult -> TLAIdentifierOrTuple.Tuple(seqResult.getLocation(), seqResult.get(ids)));
	}
	
	static Grammar<TLAIdentifierOrTuple> parseIdentifierOrTuple() {
		return parseOneOf(
				parseTLAIdentifier()
						.map(TLAIdentifierOrTuple::Identifier),
				parseIdentifierTuple());
	}
	
	static Grammar<TLAQuantifierBound> parseQuantifierBound(){
		Variable<LocatedList<TLAIdentifier>> ids = new Variable<>("ids");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return parseOneOf(
				sequence(
						part(ids, parseIdentifierTuple()
								.map(t -> new LocatedList<>(t.getLocation(), t.getTuple()))),
						drop(parseTLAToken("\\in")),
						part(expr, EXPRESSION)
				).map(seqResult -> new TLAQuantifierBound(
						seqResult.getLocation(), TLAQuantifierBound.Type.TUPLE, seqResult.get(ids),
						seqResult.get(expr))),
				sequence(
						part(ids, parseCommaList(parseTLAIdentifier())),
						drop(parseTLAToken("\\in")),
						part(expr, EXPRESSION)
				).map(seqResult -> new TLAQuantifierBound(
						seqResult.getLocation(), TLAQuantifierBound.Type.IDS, seqResult.get(ids),
						seqResult.get(expr)
				))
		);
	}
	
	static Grammar<LocatedList<TLAGeneralIdentifierPart>> parseInstancePrefix(){
		return repeat(scope(() -> {
			Variable<TLAIdentifier> id = new Variable<>("id");
			Variable<LocatedList<TLAExpression>> args = new Variable<>("args");
			return sequence(
					part(id, parseTLAIdentifier()),
					part(args, parseOneOf(
							scope(() -> {
								Variable<LocatedList<TLAExpression>> innerArgs = new Variable<>("innerArgs");
								return sequence(
										drop(parseTLAToken("(")),
										part(innerArgs, parseCommaList(EXPRESSION)),
										drop(parseTLAToken(")"))
								).map(seqResult -> seqResult.get(innerArgs));
							}),
							nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
					)),
					drop(parseTLAToken("!"))
			).map(seqResult ->
					new TLAGeneralIdentifierPart(seqResult.getLocation(), seqResult.get(id), seqResult.get(args)));
		}));
	}
	
	static Grammar<TLAExpression> parseTupleExpression(){
		Variable<LocatedList<TLAExpression>> exprs = new Variable<>("exprs");
		return sequence(
				drop(parseTLAToken("<<")),
				part(exprs, parseOneOf(
						parseCommaList(EXPRESSION),
						nop().map(n -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseTLAToken(">>"))
				).map(seqResult -> new TLATuple(seqResult.getLocation(), seqResult.get(exprs)));
	}
	
	static Grammar<TLAExpression> parseRequiredActionExpression(){
		Variable<TLAExpression> expr = new Variable<>("expr");
		Variable<TLAExpression> vars = new Variable<>("vars");
		return sequence(
				drop(parseTLAToken("<<")),
				part(expr, EXPRESSION),
				drop(parseTLAToken(">>_")),
				part(vars, EXPRESSION)
		).map(seqResult ->
				new TLARequiredAction(seqResult.getLocation(), seqResult.get(expr), seqResult.get(vars)));
	}
	
	static Grammar<TLAExpression> parseInnerPrefixOperator(){
		Variable<LocatedList<TLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<Located<String>> token = new Variable<>("token");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				part(prefix, parseInstancePrefix()),
				part(token, parseTLATokenOneOf(PREFIX_OPERATORS)),
				part(expr, EXPRESSION)
		).map(seqResult -> {
			Located<String> tokenV = seqResult.get(token);
			return new TLAUnary(
					seqResult.getLocation(),
					new TLASymbol(tokenV.getLocation(), tokenV.getValue()),
					seqResult.get(prefix), seqResult.get(expr));
		});
	}
	
	static Grammar<TLAExpression> parseOperatorCall(){
		Variable<LocatedList<TLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<TLAIdentifier> id = new Variable<>("id");
		Variable<LocatedList<TLAExpression>> args = new Variable<>("args");
		return sequence(
				part(prefix, parseInstancePrefix()),
				part(id, parseTLAIdentifier()),
				drop(parseTLAToken("(")),
				part(args, parseCommaList(EXPRESSION)),
				drop(parseTLAToken(")"))
		).map(seqResult -> new TLAOperatorCall(seqResult.getLocation(), seqResult.get(id),
				seqResult.get(prefix), seqResult.get(args)));
	}
	
	static Grammar<TLAExpression> parseGeneralIdentifier(){
		Variable<LocatedList<TLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<TLAIdentifier> id = new Variable<>("id");
		return sequence(
				part(prefix, parseInstancePrefix()),
				part(id, parseTLAIdentifier())
		).map(seqResult -> new TLAGeneralIdentifier(seqResult.getLocation(), seqResult.get(id),
				seqResult.get(prefix)));
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
		Grammar<Located<ConjunctDisjunctPart>> partGrammar = scope(() -> {
			Variable<Located<Void>> op = new Variable<>("op");
			Variable<TLAExpression> expr = new Variable<>("expr");
			Variable<Located<Integer>> next = new Variable<>("next");
			return sequence(
					part(op, parseTLAToken(which)),
					part(next, access(info -> {
						Located<Void> opV = info.get(op);
						return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn()+1);
					})),
					part(expr, EXPRESSION.substitute(next, MIN_COLUMN))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new ConjunctDisjunctPart(
							seqResult.get(op),
							seqResult.get(expr))));
		});

		ReferenceGrammar<Located<ConjunctDisjunctPart>> refPartGrammar = new ReferenceGrammar<>(
				argument(MIN_COLUMN, partGrammar).compile());

		Variable<Located<ConjunctDisjunctPart>> part1 = new Variable<>("part1");
		Variable<LocatedList<Located<ConjunctDisjunctPart>>> parts2 = new Variable<>("parts2");
		Variable<Located<Integer>> next2 = new Variable<>("next2");
		return sequence(
				part(part1, partGrammar),
				part(next2, access(info -> {
					Located<Void> opV = info.get(part1).getValue().getSymLocation();
					return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn());
				})),
				part(parts2, repeat(refPartGrammar.substitute(next2, MIN_COLUMN)))
		).map(seqResult -> {
			Located<ConjunctDisjunctPart> part1V = seqResult.get(part1);
			LocatedList<Located<ConjunctDisjunctPart>> parts2V = seqResult.get(parts2);

			if(parts2V.isEmpty()) return part1V.getValue().getExpr();

			Located<ConjunctDisjunctPart> firstRHS = parts2V.get(0);
			TLAExpression lhs = new TLABinOp(
					part1V.getLocation().combine(firstRHS.getLocation()),
					new TLASymbol(firstRHS.getValue().getSymLocation().getLocation(), which),
					Collections.emptyList(),
					part1V.getValue().getExpr(),
					firstRHS.getValue().getExpr());
			for(Located<ConjunctDisjunctPart> rhs : parts2V.subList(1, parts2V.size())) {
				lhs = new TLABinOp(
						lhs.getLocation().combine(rhs.getLocation()),
						new TLASymbol(rhs.getValue().getSymLocation().getLocation(), which),
						Collections.emptyList(), lhs, rhs.getValue().getExpr());
			}
			return lhs;
		});
	}
	
	static Grammar<TLAExpression> parseDisjunct(){
		return parseConjunctOrDisjunct("\\/");
	}
	
	static Grammar<TLAExpression> parseIfExpression(){
		Variable<TLAExpression> ifexpr = new Variable<>("ifexpr");
		Variable<TLAExpression> thenexpr = new Variable<>("thenexpr");
		Variable<TLAExpression> elseexpr = new Variable<>("elseexpr");
		return sequence(
				drop(parseTLAToken("IF")),
				part(ifexpr, EXPRESSION),
				drop(parseTLAToken("THEN")),
				part(thenexpr, EXPRESSION),
				drop(parseTLAToken("ELSE")),
				part(elseexpr, EXPRESSION)
		).map(seqResult -> new TLAIf(
				seqResult.getLocation(), seqResult.get(ifexpr), seqResult.get(thenexpr), seqResult.get(elseexpr)));
	}
	
	public static Grammar<TLAExpression> parseCaseExpression(){
		Variable<TLACaseArm> firstArm = new Variable<>("firstArm");
		Variable<LocatedList<TLACaseArm>> arms = new Variable<>("arms");
		Variable<Located<TLAExpression>> other = new Variable<>("other");
		return sequence(
				drop(parseTLAToken("CASE")),
				part(firstArm, scope(() -> {
					Variable<TLAExpression> cond = new Variable<>("cond");
					Variable<TLAExpression> result = new Variable<>("result");
					return sequence(
							part(cond, EXPRESSION),
							drop(parseTLAToken("->")),
							part(result, EXPRESSION)
					).map(seqResult ->
							new TLACaseArm(seqResult.getLocation(), seqResult.get(cond), seqResult.get(result)));
				})),
				part(arms, repeat(scope(() -> {
					Variable<TLAExpression> cond = new Variable<>("cond");
					Variable<TLAExpression> result = new Variable<>("result");
					return sequence(
							drop(parseTLAToken("[]")),
							part(cond, EXPRESSION),
							drop(parseTLAToken("->")),
							part(result, EXPRESSION)
					).map(seqResult ->
							new TLACaseArm(seqResult.getLocation(), seqResult.get(cond), seqResult.get(result)));
				}))),
				part(other, parseOneOf(
						scope(() -> {
							Variable<TLAExpression> other2 = new Variable<>("other2");
							return sequence(
									drop(parseTLAToken("[]")),
									drop(parseTLAToken("OTHER")),
									drop(parseTLAToken("->")),
									part(other2, EXPRESSION)
							).map(seqResult -> new Located<>(seqResult.getLocation(), seqResult.get(other2)));
						}),
						nop().map(v -> new Located<>(v.getLocation(), null))
				))
		).map(seqResult -> {
			LocatedList<TLACaseArm> armsV = seqResult.get(arms);
			armsV.add(0, seqResult.get(firstArm));
			return new TLACase(seqResult.getLocation(), armsV, seqResult.get(other).getValue());
		});
	}
	
	static Grammar<TLAExpression> parseFunctionExpression(){
		Variable<LocatedList<TLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<TLAExpression> body = new Variable<>("body");
		return sequence(
				drop(parseTLAToken("[")),
				part(bounds, parseCommaList(parseQuantifierBound())),
				drop(parseTLAToken("|->")),
				part(body, EXPRESSION),
				drop(parseTLAToken("]"))
				).map(seqResult -> new TLAFunction(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(body)));
	}
	
	static Grammar<TLAExpression> parseRecordSetExpression(){
		Variable<LocatedList<TLARecordSet.Field>> fields = new Variable<>("fields");
		return sequence(
				drop(parseTLAToken("[")),
				part(fields, parseCommaList(scope(() -> {
					Variable<TLAIdentifier> id = new Variable<>("id");
					Variable<TLAExpression> set = new Variable<>("set");
					return sequence(
							part(id, parseTLAIdentifier()),
							drop(parseTLAToken(":")),
							part(set, EXPRESSION)
					).map(seqResult -> new TLARecordSet.Field(
							seqResult.getLocation(), seqResult.get(id), seqResult.get(set)));
				}))),
				drop(parseTLAToken("]"))
		).map(seqResult -> new TLARecordSet(seqResult.getLocation(), seqResult.get(fields)));
	}
	
	static Grammar<TLAExpression> parseRecordConstructorExpression(){
		Variable<LocatedList<TLARecordConstructor.Field>> fields = new Variable<>("fields");
		return sequence(
				drop(parseTLAToken("[")),
				part(fields, parseCommaList(scope(() -> {
					Variable<TLAIdentifier> id = new Variable<>("id");
					Variable<TLAExpression> set = new Variable<>("set");
					return sequence(
							part(id, parseTLAIdentifier()),
							drop(parseTLAToken("|->")),
							part(set, EXPRESSION)
					).map(seqResult -> new TLARecordConstructor.Field(seqResult.getLocation(), seqResult.get(id), seqResult.get(set)));
				}))),
				drop(parseTLAToken("]"))
		).map(seqResult -> new TLARecordConstructor(seqResult.getLocation(), seqResult.get(fields)));
	}
	
	static Grammar<TLAExpression> parseFunctionSetExpression(){
		Variable<TLAExpression> from = new Variable<>("from");
		Variable<TLAExpression> to = new Variable<>("to");
		return sequence(
				drop(parseTLAToken("[")),
				part(from, EXPRESSION),
				drop(parseTLAToken("->")),
				part(to, EXPRESSION),
				drop(parseTLAToken("]"))
		).map(seqResult -> new TLAFunctionSet(seqResult.getLocation(), seqResult.get(from), seqResult.get(to)));
	}
	
	static Grammar<TLAExpression> parseMaybeActionExpression(){
		Variable<TLAExpression> expr = new Variable<>("expr");
		Variable<TLAExpression> vars = new Variable<>("vars");
		return sequence(
				drop(parseTLAToken("[")),
				part(expr, EXPRESSION),
				drop(parseTLAToken("]_")),
				part(vars, EXPRESSION)
		).map(seqResult -> new TLAMaybeAction(seqResult.getLocation(), seqResult.get(expr), seqResult.get(vars)));
	}
	
	static Grammar<TLAExpression> parseFunctionSubstitutionExpression(){
		Variable<TLAExpression> expr = new Variable<>("expr");
		Variable<LocatedList<TLAFunctionSubstitutionPair>> subs = new Variable<>("subs");
		return sequence(
				drop(parseTLAToken("[")),
				part(expr, EXPRESSION),
				drop(parseTLAToken("EXCEPT")),
				part(subs, parseCommaList(scope(() -> {
					Variable<LocatedList<TLASubstitutionKey>> keys = new Variable<>("keys");
					Variable<TLAExpression> value = new Variable<>("value");
					return sequence(
							drop(parseTLAToken("!")),
							part(keys, repeatOneOrMore(
									parseOneOf(
											scope(() -> {
												Variable<TLAIdentifier> id = new Variable<>("id");
												return sequence(
														drop(parseTLAToken(".")),
														part(id, parseTLAIdentifier())
												).map(seqResult -> new TLASubstitutionKey(
														seqResult.getLocation(),
														Collections.singletonList(new TLAString(
																seqResult.get(id).getLocation(),
																seqResult.get(id).getId()))));
											}),
											scope(() -> {
												Variable<LocatedList<TLAExpression>> indices = new Variable<>("indices");
												return sequence(
														drop(parseTLAToken("[")),
														part(indices, parseCommaList(EXPRESSION)),
														drop(parseTLAToken("]"))
												).map(seqResult -> new TLASubstitutionKey(
														seqResult.getLocation(),
														seqResult.get(indices)));
											})
									))),
							drop(parseTLAToken("=")),
							part(value, EXPRESSION)
					).map(seqResult -> new TLAFunctionSubstitutionPair(
							seqResult.getLocation(),
							seqResult.get(keys),
							seqResult.get(value)));
				}))),
				drop(parseTLAToken("]"))
		).map(seqResult -> new TLAFunctionSubstitution(seqResult.getLocation(), seqResult.get(expr), seqResult.get(subs)));
	}
	
	static Grammar<TLAExpression> parseGroupExpression(){
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseTLAToken("(")),
				part(expr, EXPRESSION),
				drop(parseTLAToken(")"))
		).map(seqResult -> seqResult.get(expr));
	}
	
	static Grammar<TLAExpression> parseQuantifiedExistentialExpression(){
		Variable<LocatedList<TLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseTLAToken("\\E")),
				part(bounds, parseCommaList(parseQuantifierBound())),
				drop(parseTLAToken(":")),
				part(expr, EXPRESSION)
		).map(seqResult -> new TLAQuantifiedExistential(
				seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}

	static Grammar<TLAExpression> parseQuantifiedUniversalExpression(){
		Variable<LocatedList<TLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseTLAToken("\\A")),
				part(bounds, parseCommaList(parseQuantifierBound())),
				drop(parseTLAToken(":")),
				part(expr, EXPRESSION)
		).map(seqResult -> new TLAQuantifiedUniversal(
				seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<TLAExpression> parseUnquantifiedExistentialExpression(){
		Variable<LocatedList<TLAIdentifier>> bounds = new Variable<>("bounds");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseOneOf(
						parseTLAToken("\\E"),
						parseTLAToken("\\EE"))),
				part(bounds, parseCommaList(parseTLAIdentifier())),
				drop(parseTLAToken(":")),
				part(expr, EXPRESSION)
		).map(seqResult -> new TLAExistential(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<TLAExpression> parseUnquantifiedUniversalExpression(){
		Variable<LocatedList<TLAIdentifier>> bounds = new Variable<>("bounds");
		Variable<TLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseOneOf(
						parseTLAToken("\\A"),
						parseTLAToken("\\AA"))),
				part(bounds, parseCommaList(parseTLAIdentifier())),
				drop(parseTLAToken(":")),
				part(expr, EXPRESSION)
		).map(seqResult -> new TLAUniversal(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<TLAExpression> parseSetConstructorExpression(){
		Variable<LocatedList<TLAExpression>> members = new Variable<>("members");
		return sequence(
				drop(parseTLAToken("{")),
				part(members, parseOneOf(
						parseCommaList(EXPRESSION),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseTLAToken("}"))
		).map(seqResult -> new TLASetConstructor(seqResult.getLocation(), seqResult.get(members)));
	}
	
	static Grammar<TLAExpression> parseSetRefinementExpression(){
		Variable<TLAIdentifierOrTuple> ids = new Variable<>("ids");
		Variable<TLAExpression> set = new Variable<>("set");
		Variable<TLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parseTLAToken("{")),
				part(ids, parseIdentifierOrTuple()),
				drop(parseTLAToken("\\in")),
				part(set, EXPRESSION),
				drop(parseTLAToken(":")),
				part(condition, EXPRESSION),
				drop(parseTLAToken("}"))
		).map(seqResult -> new TLASetRefinement(seqResult.getLocation(), seqResult.get(ids), seqResult.get(set), seqResult.get(condition)));
	}
	
	static Grammar<TLAExpression> parseSetComprehensionExpression(){
		Variable<TLAExpression> generator = new Variable<>("generator");
		Variable<LocatedList<TLAQuantifierBound>> sets = new Variable<>("sets");
		return sequence(
				drop(parseTLAToken("{")),
				part(generator, EXPRESSION),
				drop(parseTLAToken(":")),
				part(sets, parseCommaList(parseQuantifierBound())),
				drop(parseTLAToken("}"))
		).map(seqResult -> new TLASetComprehension(seqResult.getLocation(), seqResult.get(generator), seqResult.get(sets)));
	}
	
	static Grammar<TLAExpression> parseLetExpression(){
		Variable<LocatedList<TLAUnit>> units = new Variable<>("units");
		Variable<TLAExpression> body = new Variable<>("body");
		return sequence(
				drop(parseTLAToken("LET")),
				part(units, repeatOneOrMore(
						parseOneOf(
								parseOperatorDefinition(false),
								parseFunctionDefinition(false),
								parseModuleDefinition(false)
								))),
				drop(parseTLAToken("IN")),
				part(body, EXPRESSION)
				).map(seqResult -> new TLALet(seqResult.getLocation(), seqResult.get(units), seqResult.get(body)));
	}

	static Grammar<TLAExpression> parseFairnessConstraint(){
		Variable<Located<TLAFairness.Type>> type = new Variable<>("type");
		Variable<TLAExpression> vars = new Variable<>("vars");
		Variable<TLAExpression> expression = new Variable<>("expression");
		return sequence(
				part(type, parseOneOf(
						parseTLAToken("WF_").map(v ->
								new Located<>(v.getLocation(), TLAFairness.Type.WEAK)),
						parseTLAToken("SF_").map(v ->
								new Located<>(v.getLocation(), TLAFairness.Type.STRONG))
				)),
				part(vars, EXPRESSION),
				drop(parseTLAToken("(")),
				part(expression, EXPRESSION),
				drop(parseTLAToken(")"))
		).map(seq -> new TLAFairness(
				seq.getLocation(), seq.get(type).getValue(), seq.get(vars), seq.get(expression)));
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

	public static final Map<Integer, ReferenceGrammar<TLAExpression>> OPERATORS_BY_PRECEDENCE = new HashMap<>(17);
	static {
		for(int i = 1; i <= 18; ++i){
			OPERATORS_BY_PRECEDENCE.put(i, new ReferenceGrammar<TLAExpression>()
					.substitute(MIN_COLUMN, MIN_COLUMN));
		}
	}
	public static final ReferenceGrammar<TLAExpression> EXPRESSION_NO_OPERATORS =
			new ReferenceGrammar<TLAExpression>().substitute(MIN_COLUMN, MIN_COLUMN);
	public static final ReferenceGrammar<TLAExpression> EXPRESSION = OPERATORS_BY_PRECEDENCE.get(1);

	private static Grammar<TLAExpression> parsePrefixOperator(int precedence) {
		List<String> operatorOptions = PREFIX_OPERATORS
				.stream()
				.filter(op ->
						/*precedence >= PREFIX_OPERATORS_LOW_PRECEDENCE.get(op)
								&& */precedence <= PREFIX_OPERATORS_HI_PRECEDENCE.get(op))
				.collect(Collectors.toList());

		System.out.println("prefix precedence "+precedence+" "+operatorOptions);

		if(operatorOptions.isEmpty()) return parseOneOf(Collections.emptyList());

		ReferenceGrammar<TLAExpression> self = new ReferenceGrammar<>();

		Variable<LocatedList<TLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");

		List<Grammar<? extends TLAExpression>> options = new ArrayList<>();
		for(String operator : operatorOptions) {
			options.add(scope(() -> {
				Variable<Located<Void>> op = new Variable<>("op");
				Variable<TLAExpression> expr = new Variable<>("expr");
				System.out.println("prefix recurse "+operator+" "+(PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1));
				return sequence(
						part(op, parseTLAToken(operator)),
						part(expr, parseOneOf(
								self,
								OPERATORS_BY_PRECEDENCE.get(PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)
						))
				).map(seqResult -> {
					int p = precedence;
					LocatedList<TLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
					Located<Void> opV = seqResult.get(op);
					//System.out.println("prefix "+precedence+" "+operator);
					return new TLAUnary(
							prefixV.getLocation().combine(seqResult.getLocation()),
							new TLASymbol(opV.getLocation(), operator),
							prefixV,
							seqResult.get(expr));
				});
			}));
		}

		Variable<TLAExpression> result = new Variable<>("prefixOpResult");
		Grammar<TLAExpression> selfGrammar = sequence(
					part(prefix, parseInstancePrefix()),
					part(result, parseOneOf(options))
		).map(seqResult -> seqResult.get(result));

		self.setReferencedGrammar(selfGrammar.compile());

		return selfGrammar;
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
		Variable<TLAExpression> lhs = new Variable<>("lhs");
		Variable<LocatedList<TLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");

		List<Grammar<? extends TLAExpression>> afterOptions = new ArrayList<>();
		for(String operator : INFIX_OPERATORS) {
			if(INFIX_OPERATORS_LOW_PRECEDENCE.get(operator) <= precedence
					&& INFIX_OPERATORS_HI_PRECEDENCE.get(operator) >= precedence) {
				System.out.println("precedence "+precedence+" "+operator);
				Variable<Located<Void>> op = new Variable<>("op");
				Variable<TLAExpression> rhs = new Variable<>("rhs");
				Variable<LocatedList<Located<InfixOperatorPart>>> leftAssociativeParts = new Variable<>("leftAssociativeParts");
				afterOptions.add(
						sequence(
								part(op, parseInfixOperator(operator)),
								part(rhs, OPERATORS_BY_PRECEDENCE.get(INFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)),
								part(leftAssociativeParts, INFIX_OPERATORS_LEFT_ASSOCIATIVE.contains(operator) ?
										scope(() -> {
											Variable<LocatedList<TLAGeneralIdentifierPart>> prefix2 = new Variable<>("prefix2");
											Variable<Located<Void>> op2 = new Variable<>("op2");
											Variable<TLAExpression> rhs2 = new Variable<>("rhs2");
											return repeat(sequence(
													part(prefix2, parseInstancePrefix()),
													part(op2, parseInfixOperator(operator)),
													part(rhs2, OPERATORS_BY_PRECEDENCE.get(INFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1))
											).map(seqResult -> new Located<>(seqResult.getLocation(), new InfixOperatorPart(
													seqResult.get(prefix2), seqResult.get(op2), seqResult.get(rhs2), null))));
										})
										: nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList())))
						).map(seqResult -> {
							int p = precedence;
							TLAExpression lhsV = seqResult.get(lhs);
							LocatedList<TLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
							Located<Void> opV = seqResult.get(op);
							lhsV = new TLABinOp(
									seqResult.getLocation().combine(prefixV.getLocation()).combine(lhsV.getLocation()),
									new TLASymbol(opV.getLocation(), operator),
									prefixV,
									lhsV,
									seqResult.get(rhs));

							for(Located<InfixOperatorPart> part : seqResult.get(leftAssociativeParts)) {
								lhsV = new TLABinOp(
										part.getLocation().combine(lhsV.getLocation()).combine(part.getLocation()),
										new TLASymbol(part.getValue().getSymLocation().getLocation(), operator),
										part.getValue().getPrefix(),
										lhsV,
										part.getValue().getRhs());
							}
							return lhsV;
						})
				);
			}
		}

		List<String> relevantPostfixOperators = POSTFIX_OPERATORS
				.stream()
				.filter(operator -> POSTFIX_OPERATORS_PRECEDENCE.get(operator) >= precedence)
				.collect(Collectors.toList());

		Supplier<Grammar<Located<PostfixOperatorPart>>> functionCallGrammar = () -> {
			Variable<LocatedList<TLAExpression>> arguments = new Variable<>("arguments");
			return sequence(
					drop(parseTLAToken("[")),
					part(arguments, parseCommaList(EXPRESSION)),
					drop(parseTLAToken("]"))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new PostfixOperatorPart(null, null, seqResult.get(arguments), true)));
		};

		Supplier<Grammar<Located<PostfixOperatorPart>>> postfixPartsGrammar = () -> {
			Grammar<Located<PostfixOperatorPart>> operatorGrammar = scope(() -> {
				Variable<LocatedList<TLAGeneralIdentifierPart>> prefix2 = new Variable<>("prefix2");
				Variable<Located<String>> op2 = new Variable<>("op2");
				return sequence(
						part(prefix2, parseInstancePrefix()),
						part(op2, parseTLATokenOneOf(relevantPostfixOperators))
				).map(seqResult -> new Located<>(
						seqResult.getLocation(),
						new PostfixOperatorPart(seqResult.get(prefix), seqResult.get(op2), null, false)));
			});

			return precedence <= 16 ?
					parseOneOf(operatorGrammar, functionCallGrammar.get())
					: operatorGrammar;
		};

		{

			Variable<Located<String>> op = new Variable<>("op");
			Variable<LocatedList<Located<PostfixOperatorPart>>> repeatedPostfixParts = new Variable<>("repeatedPostfixParts");
			afterOptions.add(
					sequence(
							part(op, parseTLATokenOneOf(relevantPostfixOperators)),
							part(repeatedPostfixParts, repeat(postfixPartsGrammar.get()))
					).map(seqResult -> {
						TLAExpression lhsV = seqResult.get(lhs);
						LocatedList<TLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
						Located<String> opV = seqResult.get(op);
						lhsV = new TLAUnary(
								lhsV.getLocation().combine(prefixV.getLocation()).combine(opV.getLocation()),
								new TLASymbol(opV.getLocation(), opV.getValue()),
								prefixV,
								lhsV);
						return buildPostfixExpression(lhsV, seqResult.get(repeatedPostfixParts));
					}));
		}

		Variable<TLAExpression> extendedResult = new Variable<>("extendedResult");
		return sequence(
				part(lhs, OPERATORS_BY_PRECEDENCE.get(precedence+1)),
				parseOneOf(
						sequence(
								part(prefix, parseInstancePrefix()),
								part(extendedResult, parseOneOf(afterOptions))
						).map(seqResult -> new Located<>(seqResult.getLocation(), null)),
						precedence <= 16 ? parseOneOf(
								part(extendedResult, scope(() -> {
									Variable<Located<PostfixOperatorPart>> fnCall = new Variable<>("fnCall");
									Variable<LocatedList<Located<PostfixOperatorPart>>> remainingParts = new Variable<>("remainingParts");
									return sequence(
											part(fnCall, functionCallGrammar.get()),
											part(remainingParts, repeat(postfixPartsGrammar.get()))
									).map(seqResult -> {
										Located<PostfixOperatorPart> fnCallV = seqResult.get(fnCall);
										TLAExpression lhsV = seqResult.get(lhs);
										return buildPostfixExpression(
												new TLAFunctionCall(
														lhsV.getLocation().combine(fnCallV.getLocation()),
														lhsV,
														fnCallV.getValue().getFunctionArguments()),
												seqResult.get(remainingParts));
									});
								})),
								part(extendedResult, access(info -> info.get(lhs)))
						) : part(extendedResult, access(info -> info.get(lhs)))
				)
		).map(seqResult -> seqResult.get(extendedResult));
	}

	private static Grammar<Located<Void>> parseInfixOperator(String operator) {
		List<String> supersets = new ArrayList<>();
		for(String possibleSuperset : INFIX_OPERATORS) {
			if(possibleSuperset.length() > operator.length() && possibleSuperset.startsWith(operator)) {
				supersets.add(possibleSuperset);
			}
		}

		if(supersets.isEmpty()) return parseTLAToken(operator);

		Variable<Located<Void>> result = new Variable<>("operator");

		List<Grammar<Located<Void>>> parts = new ArrayList<>();
		parts.add(part(result, parseTLAToken(operator)));
		for(String s : supersets) {
			parts.add(reject(matchString(s.substring(operator.length()))));
		}
		return sequence(parts).map(seqResult -> seqResult.get(result));
	}

	static {
		for(int i = 1; i <= 17; ++i){
			OPERATORS_BY_PRECEDENCE.get(i).setReferencedGrammar(
					argument(MIN_COLUMN,
							parseOneOf(
									parseExpressionFromPrecedence(i),
									parsePrefixOperator(i)
							)
					).compile());
		}
		OPERATORS_BY_PRECEDENCE.get(18).setReferencedGrammar(argument(MIN_COLUMN, EXPRESSION_NO_OPERATORS).compile());
	}
	static {
		EXPRESSION_NO_OPERATORS.setReferencedGrammar(argument(MIN_COLUMN, parseOneOf(
				parseTLANumber(),
				parseTLAString(),
				parseTLATokenOneOf(
						Arrays.asList("TRUE", "FALSE"))
						.map(b -> new TLABool(b.getLocation(), b.getValue().equals("TRUE"))),

				parseGroupExpression(),
				parseTupleExpression(),

				parseRequiredActionExpression(),

				// if we find a prefix operator here, it means we hit the following situation:
				// a higher precedence prefix operator followed by a lower precedence prefix operator
				// we parse the second operator here as there is no good way to notice it "on the way down"
				//parseInnerPrefixOperator(),

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
		)).compile());
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
		Variable<TLAExpression> result = new Variable<>("result");
		return sequence(
				part(MIN_COLUMN, nop().map(v -> new Located<>(v.getLocation(), -1))),
				part(result, EXPRESSION)
		).map(seqResult -> seqResult.get(result));
	}
	
	static Grammar<TLAOpDecl> parseOpDecl(){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<Located<String>> op = new Variable<>("op");
		Variable<LocatedList<Located<Void>>> args = new Variable<>("args");
		return parseOneOf(
				sequence(
						part(name, parseTLAIdentifier()),
						drop(parseTLAToken("(")),
						part(args, parseCommaList(parseTLAToken("_"))),
						drop(parseTLAToken(")"))
				).map(seqResult ->
						TLAOpDecl.Named(seqResult.getLocation(), seqResult.get(name), seqResult.get(args).size())),
				parseTLAIdentifier().map(id -> TLAOpDecl.Id(id.getLocation(), id)),
				sequence(
						part(op, parseTLATokenOneOf(PREFIX_OPERATORS)),
						drop(parseTLAToken("_"))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					// operator - is the only operator that is both unary and binary, and can be defined as
					// both simultaneously. We special-case the unary version by renaming it.
					String value = opV.getValue().equals("-") ? "-_" : opV.getValue();
					return TLAOpDecl.Prefix(
							seqResult.getLocation(),
							new TLAIdentifier(opV.getLocation(), value));
				}),
				sequence(
						drop(parseTLAToken("_")),
						part(op, parseTLATokenOneOf(INFIX_OPERATORS)),
						drop(parseTLAToken("_"))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					return TLAOpDecl.Infix(
							seqResult.getLocation(),
							new TLAIdentifier(opV.getLocation(), opV.getValue()));
				}),
				sequence(
						drop(parseTLAToken("_")),
						part(op, parseTLATokenOneOf(POSTFIX_OPERATORS))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					return TLAOpDecl.Postfix(
							seqResult.getLocation(),
							new TLAIdentifier(opV.getLocation(), opV.getValue()));
				})
		);
	}
	
	static Grammar<TLAUnit> parseOperatorDefinition(boolean isLocal){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<TLAOpDecl>> args = new Variable<>("args");
		Variable<TLAExpression> body = new Variable<>("body");
		return sequence(
				part(args, parseOneOf(
						scope(() -> {
							Variable<Located<String>> op = new Variable<>("op");
							Variable<TLAIdentifier> rhs = new Variable<>("rhs");
							return sequence(
									part(op, parseTLATokenOneOf(PREFIX_OPERATORS)),
									part(rhs, parseTLAIdentifier()),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										// operator - is the only operator that is both unary and binary, and can
										// be defined as both simultaneously. We special-case the unary version by
										// renaming it.
										String value = opV.getValue().equals("-") ? "-_" : opV.getValue();
										return new TLAIdentifier(opV.getLocation(), value);
									}))
							).map(seqResult -> {
								TLAIdentifier rhsV = seqResult.get(rhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Collections.singletonList(TLAOpDecl.Id(rhsV.getLocation(), rhsV)));
							});
						}),
						scope(() -> {
							Variable<TLAIdentifier> lhs = new Variable<>("lhs");
							Variable<Located<String>> op = new Variable<>("op");
							Variable<TLAIdentifier> rhs = new Variable<>("rhs");
							return sequence(
									part(lhs, parseTLAIdentifier()),
									part(op, parseTLATokenOneOf(INFIX_OPERATORS)),
									part(rhs, parseTLAIdentifier()),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										return new TLAIdentifier(opV.getLocation(), opV.getValue());
									}))
							).map(seqResult -> {
								TLAIdentifier lhsV = seqResult.get(lhs);
								TLAIdentifier rhsV = seqResult.get(rhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Arrays.asList(
												TLAOpDecl.Id(lhsV.getLocation(), lhsV),
												TLAOpDecl.Id(rhsV.getLocation(), rhsV)
										));
							});
						}),
						scope(() -> {
							Variable<TLAIdentifier> lhs = new Variable<>("lhs");
							Variable<Located<String>> op = new Variable<>("op");
							return sequence(
									part(lhs, parseTLAIdentifier()),
									part(op, parseTLATokenOneOf(POSTFIX_OPERATORS)),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										return new TLAIdentifier(opV.getLocation(), opV.getValue());
									}))
							).map(seqResult -> {
								TLAIdentifier lhsV = seqResult.get(lhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Collections.singletonList(TLAOpDecl.Id(
												lhsV.getLocation(), lhsV)));
							});
						}),
						scope(() -> sequence(
								part(name, parseTLAIdentifier()),
								part(args, parseOneOf(
										sequence(
												drop(parseTLAToken("(")),
												part(args, parseCommaList(parseOpDecl())),
												drop(parseTLAToken(")"))
										).map(seqResult -> seqResult.get(args)),
										nop().map(vv -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
								))
						).map(seqResult -> seqResult.get(args)))
				)),
				drop(parseTLAToken("==")),
				part(body, parseExpression())
		).map(seqResult -> new TLAOperatorDefinition(
				seqResult.getLocation(), seqResult.get(name), seqResult.get(args), seqResult.get(body), isLocal));
	}
	
	static Grammar<TLAUnit> parseFunctionDefinition(boolean isLocal){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<TLAQuantifierBound>> args = new Variable<>("args");
		Variable<TLAExpression> body = new Variable<>("body");
		return sequence(
				part(name, parseTLAIdentifier()),
				drop(parseTLAToken("[")),
				part(args, parseCommaList(parseQuantifierBound())),
				drop(parseTLAToken("]")),
				drop(parseTLAToken("==")),
				part(body, parseExpression())
		).map(seqResult -> new TLAFunctionDefinition(
				seqResult.getLocation(),
				seqResult.get(name),
				new TLAFunction(seqResult.getLocation(), seqResult.get(args), seqResult.get(body)),
				isLocal));
	}
	
	static Grammar<TLAInstance> parseInstance(boolean isLocal){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<TLAInstance.Remapping>> remappings = new Variable<>("remappings");
		return sequence(
				drop(parseTLAToken("INSTANCE")),
				part(name, parseTLAIdentifier()),
				part(remappings, parseOneOf(
						sequence(
								drop(parseTLAToken("WITH")),
								part(remappings, parseCommaList(scope(() -> {
									Variable<TLAIdentifier> from = new Variable<>("from");
									Variable<TLAExpression> to = new Variable<>("to");
									return sequence(
											part(from, parseOneOf(
													parseTLAIdentifier(),
													parseTLATokenOneOf(PREFIX_OPERATORS).map(op ->
															new TLAIdentifier(op.getLocation(), op.getValue())),
													parseTLATokenOneOf(INFIX_OPERATORS).map(op ->
															new TLAIdentifier(op.getLocation(), op.getValue())),
													parseTLATokenOneOf(POSTFIX_OPERATORS).map(op ->
															new TLAIdentifier(op.getLocation(), op.getValue()))
											)),
											drop(parseTLAToken("<-")),
											part(to, parseExpression())
									).map(seqResult -> new TLAInstance.Remapping(
											seqResult.getLocation(), seqResult.get(from), seqResult.get(to)));
								})))
						).map(seqResult -> seqResult.get(remappings))
				))
		).map(seqResult ->
				new TLAInstance(seqResult.getLocation(), seqResult.get(name), seqResult.get(remappings), isLocal));
	}
	
	static Grammar<TLAUnit> parseModuleDefinition(boolean isLocal){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<TLAOpDecl>> args = new Variable<>("args");
		Variable<TLAInstance> instance = new Variable<>("instance");
		return sequence(
				part(name, parseTLAIdentifier()),
				part(args, parseOneOf(
						sequence(
								drop(parseTLAToken("(")),
								part(args, parseCommaList(parseOpDecl())),
								drop(parseTLAToken(")"))
						).map(seqResult -> seqResult.get(args)),
						nop().map(v -> new LocatedList<>(
								SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseTLAToken("==")),
				part(instance, parseInstance(isLocal))
		).map(seqResult ->
				new TLAModuleDefinition(seqResult.getLocation(), seqResult.get(name), seqResult.get(args),
						seqResult.get(instance), isLocal));
	}
	
	static Grammar<LocatedList<TLAIdentifier>> parseExtends(){
		Variable<LocatedList<TLAIdentifier>> exts = new Variable<>("exts");
		return sequence(
				drop(parseTLAToken("EXTENDS")),
				part(exts, parseCommaList(parseTLAIdentifier()))
		).map(seqResult -> seqResult.get(exts));
	}
	
	static Grammar<TLAUnit> parseVariableDeclaration() {
		Variable<LocatedList<TLAIdentifier>> vars = new Variable<>("vars");
		return sequence(
				drop(parseTLATokenOneOf(Arrays.asList("VARIABLES", "VARIABLE"))),
				part(vars, parseCommaList(parseTLAIdentifier()))
		).map(seqResult -> new TLAVariableDeclaration(seqResult.getLocation(), seqResult.get(vars)));
	}
	
	static Grammar<TLAUnit> parseConstantDeclaration(){
		Variable<LocatedList<TLAOpDecl>> decls = new Variable<>("decls");
		return sequence(
				drop(parseTLATokenOneOf(Arrays.asList("CONSTANTS", "CONSTANT"))),
				part(decls, parseCommaList(parseOpDecl()))
		).map(seqResult -> new TLAConstantDeclaration(seqResult.getLocation(), seqResult.get(decls)));
	}
	
	static Grammar<TLAUnit> parseAssumption(){
		Variable<TLAExpression> assumption = new Variable<>("assumption");
		return sequence(
				drop(parseTLATokenOneOf(Arrays.asList("ASSUME", "ASSUMPTION", "AXIOM"))),
				part(assumption, parseExpression())
		).map(seqResult -> new TLAAssumption(seqResult.getLocation(), seqResult.get(assumption)));
	}
	
	static Grammar<TLAUnit> parseTheorem(){
		Variable<TLAExpression> theorem = new Variable<>("theorem");
		return sequence(
				drop(parseTLAToken("THEOREM")),
				part(theorem, parseExpression())
		).map(seqResult -> new TLATheorem(seqResult.getLocation(), seqResult.get(theorem)));
	}
	
	static Grammar<TLAUnit> parseUnit(){
		Variable<TLAUnit> unit = new Variable<>("unit");
		return sequence(
				part(MIN_COLUMN, nop().map(v -> new Located<>(v.getLocation(), -1))),
				drop(parseOneOf(parse4DashesOrMore(), nop())),
				part(unit, parseOneOf(
						// all local declarations (prefixed with LOCAL)
						sequence(
								drop(parseTLAToken("LOCAL")),
								part(unit, parseOneOf(
										parseInstance(true),
										parseModuleDefinition(true),
										parseFunctionDefinition(true),
										parseOperatorDefinition(true)))
						).map(seq -> seq.get(unit)),
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
				))).map(seqResult -> {
					System.out.println("unit parsed "+seqResult.get(unit));
					return seqResult.get(unit);
				});
	}

	static final Pattern TLA_BEGIN_TRANSLATION = Pattern.compile("\\\\\\*+\\s+BEGIN TRANSLATION\\s*$", Pattern.MULTILINE);
	static final Pattern TLA_END_TRANSLATION = Pattern.compile("\\\\\\*+\\s+END TRANSLATION\\s*$", Pattern.MULTILINE);

	static Grammar<Located<Void>> parseStartTranslation(){
		Variable<Located<MatchResult>> begin = new Variable<>("begin");
		return sequence(
				drop(repeat(parseOneOf(
						matchWhitespace(),
						matchTLAMultilineComment()
				))),
				part(begin, matchPattern(TLA_BEGIN_TRANSLATION))
		).map(seq -> new Located<>(seq.get(begin).getLocation(), null));
	}

	static Grammar<Located<Void>> parseEndTranslation(){
		Variable<Located<MatchResult>> end = new Variable<>("end");
		return sequence(
				drop(repeat(parseOneOf(
						matchWhitespace(),
						matchTLAMultilineComment()
				))),
				part(end, matchPattern(TLA_END_TRANSLATION))
		).map(seq -> new Located<>(seq.get(end).getLocation(), null));
	}
	
	static Grammar<TLAModule> parseModule(){
		Variable<TLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<TLAIdentifier>> exts = new Variable<>("exts");
		Variable<LocatedList<TLAUnit>> preTranslationUnits = new Variable<>("preTranslationUnits");
		Variable<LocatedList<TLAUnit>> translatedUnits = new Variable<>("translatedUnits");
		Variable<LocatedList<TLAUnit>> postTranslationUnits = new Variable<>("postTranslationUnits");

		return sequence(
				part(MIN_COLUMN, nop().map(v -> new Located<>(v.getLocation(), -1))),
				drop(findModuleStart()),
				drop(parse4DashesOrMore()),
				drop(parseTLAToken("MODULE")),
				part(name, parseTLAIdentifier()),
				drop(parse4DashesOrMore()),
				part(exts, parseOneOf(
						parseExtends(),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList())))),
				part(preTranslationUnits, repeat(
						scope(() -> {
							Variable<TLAUnit> unit = new Variable<>("unit");
							return sequence(
									// make sure we don't accidentally parse the beginning of the TLA+ translation
									reject(parseStartTranslation()),
									part(unit, UNIT)
							).map(seq -> seq.get(unit));
						}))),
				part(translatedUnits, parseOneOf(
						sequence(
								drop(parseStartTranslation()),
								nop().map(v -> {
									System.out.println("BEGIN TRANSLATION");
									return v;
								}),
								part(translatedUnits, repeat(scope(() -> {
									Variable<TLAUnit> translatedUnit = new Variable<>("translatedUnit");
									return sequence(
													reject(parseEndTranslation()),
													part(translatedUnit, UNIT)
									).map(seq -> seq.get(translatedUnit));
								}))),
								nop().map(v -> {
									System.out.println("END TRANSLATION");
									return v;
								}),
								drop(parseEndTranslation())
						).map(seqResult -> seqResult.get(translatedUnits)),
						nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList()))
				)),
				part(postTranslationUnits, repeat(UNIT)),
				drop(parse4EqualsOrMore()),
				nop().map(v -> {
					System.out.println("COMPLETED MODULE");
					return v;
				}),
				consumeAfterModuleEnd() // consume any left-over text (that is not the beginning of another module)
		).map(seqResult ->
				new TLAModule(seqResult.getLocation(), seqResult.get(name), seqResult.get(exts),
						seqResult.get(preTranslationUnits), seqResult.get(translatedUnits), seqResult.get(postTranslationUnits)));
	}

	private static final ReferenceGrammar<TLAUnit> UNIT = new ReferenceGrammar<>();
	private static final ReferenceGrammar<TLAModule> MODULE = new ReferenceGrammar<>();
	static {
		UNIT.setReferencedGrammar(parseUnit().compile());
		MODULE.setReferencedGrammar(parseModule().compile());
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