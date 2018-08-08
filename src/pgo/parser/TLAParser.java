package pgo.parser;

import pgo.model.tla.*;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.function.Function;
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
 *  {@link pgo.parser.ParseTools}. For an overview of the basic mechanics of the system, look at
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
 * 		The minColumn argument represents this constraint - if a token is found that
 * 		would otherwise match, but is at a column index lower than
 * 		minColumn, the match fails instead. This enables most of the
 * 		codebase to not have to care too much about this rule, while
 * 		consistently enforcing it.
 * 	    </p>
 *
 *      <p>
 * 		Passing {@code minColumn = -1} is used to disable this feature for
 * 		expressions that are not on the right hand side of {@code /\} or {@code \/}.
 * 	    </p>
 *
 */
public final class TLAParser {

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
	
	static Grammar<PGoTLAIdentifierOrTuple> parseIdentifierTuple(Variable<Located<Integer>> minColumn){
		Variable<LocatedList<PGoTLAIdentifier>> ids = new Variable<>("ids");
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(ids, parseOneOf(
						parseCommaList(parseIdentifier(minColumn), minColumn),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseBuiltinToken(">>", minColumn))
		).map(seqResult -> PGoTLAIdentifierOrTuple.Tuple(seqResult.getLocation(), seqResult.get(ids)));
	}
	
	static Grammar<PGoTLAIdentifierOrTuple> parseIdentifierOrTuple(Variable<Located<Integer>> minColumn) {
		return parseOneOf(
				parseIdentifier(minColumn)
						.map(PGoTLAIdentifierOrTuple::Identifier),
				parseIdentifierTuple(minColumn));
	}
	
	static Grammar<PGoTLAQuantifierBound> parseQuantifierBound(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAIdentifier>> ids = new Variable<>("ids");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return parseOneOf(
				sequence(
						part(ids, parseIdentifierTuple(minColumn)
								.map(t -> new LocatedList<>(t.getLocation(), t.getTuple()))),
						drop(parseBuiltinToken("\\in", minColumn)),
						part(expr, recExpr)
				).map(seqResult -> new PGoTLAQuantifierBound(
						seqResult.getLocation(), PGoTLAQuantifierBound.Type.TUPLE, seqResult.get(ids),
						seqResult.get(expr))),
				sequence(
						part(ids, parseCommaList(parseIdentifier(minColumn), minColumn)),
						drop(parseBuiltinToken("\\in", minColumn)),
						part(expr, recExpr)
				).map(seqResult -> new PGoTLAQuantifierBound(
						seqResult.getLocation(), PGoTLAQuantifierBound.Type.IDS, seqResult.get(ids),
						seqResult.get(expr)
				))
		);
	}
	
	static Grammar<LocatedList<PGoTLAGeneralIdentifierPart>> parseInstancePrefix(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		return repeat(scope(() -> {
			Variable<PGoTLAIdentifier> id = new Variable<>("id");
			Variable<LocatedList<PGoTLAExpression>> args = new Variable<>("args");
			return sequence(
					part(id, parseIdentifier(minColumn)),
					part(args, parseOneOf(
							scope(() -> {
								Variable<LocatedList<PGoTLAExpression>> innerArgs = new Variable<>("innerArgs");
								return sequence(
										drop(parseBuiltinToken("(", minColumn)),
										part(innerArgs, parseCommaList(recExpr, minColumn)),
										drop(parseBuiltinToken(")", minColumn))
								).map(seqResult -> seqResult.get(innerArgs));
							}),
							nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
					)),
					drop(parseBuiltinToken("!", minColumn))
			).map(seqResult ->
					new PGoTLAGeneralIdentifierPart(seqResult.getLocation(), seqResult.get(id), seqResult.get(args)));
		}));
	}
	
	static Grammar<PGoTLAExpression> parseTupleExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAExpression>> exprs = new Variable<>("exprs");
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(exprs, parseOneOf(
						parseCommaList(recExpr, minColumn),
						nop().map(n -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseBuiltinToken(">>", minColumn))
				).map(seqResult -> new PGoTLATuple(seqResult.getLocation(), seqResult.get(exprs)));
	}
	
	static Grammar<PGoTLAExpression> parseRequiredActionExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		Variable<PGoTLAExpression> vars = new Variable<>("vars");
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(expr, recExpr),
				drop(parseBuiltinToken(">>_", minColumn)),
				part(vars, recExpr)
		).map(seqResult ->
				new PGoTLARequiredAction(seqResult.getLocation(), seqResult.get(expr), seqResult.get(vars)));
	}
	
	static Grammar<PGoTLAExpression> parseInnerPrefixOperator(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<Located<String>> token = new Variable<>("token");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				part(prefix, parseInstancePrefix(minColumn, recExpr)),
				part(token, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
				part(expr, recExpr)
		).map(seqResult -> {
			Located<String> tokenV = seqResult.get(token);
			return new PGoTLAUnary(
					seqResult.getLocation(),
					new PGoTLASymbol(tokenV.getLocation(), tokenV.getValue()),
					seqResult.get(prefix), seqResult.get(expr));
		});
	}
	
	static Grammar<PGoTLAExpression> parseOperatorCall(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<PGoTLAIdentifier> id = new Variable<>("id");
		Variable<LocatedList<PGoTLAExpression>> args = new Variable<>("args");
		return sequence(
				part(prefix, parseInstancePrefix(minColumn, recExpr)),
				part(id, parseIdentifier(minColumn)),
				drop(parseBuiltinToken("(", minColumn)),
				part(args, parseCommaList(recExpr, minColumn)),
				drop(parseBuiltinToken(")", minColumn))
		).map(seqResult -> new PGoTLAOperatorCall(seqResult.getLocation(), seqResult.get(id),
				seqResult.get(prefix), seqResult.get(args)));
	}
	
	static Grammar<PGoTLAExpression> parseGeneralIdentifier(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
		Variable<PGoTLAIdentifier> id = new Variable<>("id");
		return sequence(
				part(prefix, parseInstancePrefix(minColumn, recExpr)),
				part(id, parseIdentifier(minColumn))
		).map(seqResult -> new PGoTLAGeneralIdentifier(seqResult.getLocation(), seqResult.get(id),
				seqResult.get(prefix)));
	}

	static Grammar<PGoTLAExpression> parseConjunct(Variable<Located<Integer>> minColumn, ReferenceGrammar<PGoTLAExpression> recExpr) {
		return parseConjunctOrDisjunct("/\\", minColumn, recExpr);
	}

	private static final class ConjunctDisjunctPart {
		private Located<Void> symLocation;
		private PGoTLAExpression expr;

		public ConjunctDisjunctPart(Located<Void> symLocation, PGoTLAExpression expr) {
			this.symLocation = symLocation;
			this.expr = expr;
		}

		public Located<Void> getSymLocation() {
			return symLocation;
		}

		public PGoTLAExpression getExpr() { return expr; }
	}
	
	static Grammar<PGoTLAExpression> parseConjunctOrDisjunct(String which, Variable<Located<Integer>> minColumn, ReferenceGrammar<PGoTLAExpression> recExpr){
		Grammar<Located<ConjunctDisjunctPart>> partGrammar = scope(() -> {
			Variable<Located<Void>> op = new Variable<>("op");
			Variable<PGoTLAExpression> expr = new Variable<>("expr");
			Variable<Located<Integer>> nextMinColumn = new Variable<>("nextMinColumn");
			return sequence(
					part(op, parseBuiltinToken(which, minColumn)),
					part(nextMinColumn, access(info -> {
						Located<Void> opV = info.get(op);
						return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn()+1);
					})),
					part(expr, recExpr.substitute(nextMinColumn, minColumn))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new ConjunctDisjunctPart(
							seqResult.get(op),
							seqResult.get(expr))));
		});

		ReferenceGrammar<Located<ConjunctDisjunctPart>> refPartGrammar = new ReferenceGrammar<>(
				argument(minColumn, partGrammar).compile());

		Variable<Located<ConjunctDisjunctPart>> part1 = new Variable<>("part1");
		Variable<LocatedList<Located<ConjunctDisjunctPart>>> parts2 = new Variable<>("parts2");
		Variable<Located<Integer>> nextMinColumn2 = new Variable<>("nextMinColumn2");
		return sequence(
				part(part1, partGrammar),
				part(nextMinColumn2, access(info -> {
					Located<Void> opV = info.get(part1).getValue().getSymLocation();
					return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn());
				})),
				part(parts2, repeat(refPartGrammar.substitute(nextMinColumn2, minColumn)))
		).map(seqResult -> {
			Located<ConjunctDisjunctPart> part1V = seqResult.get(part1);
			LocatedList<Located<ConjunctDisjunctPart>> parts2V = seqResult.get(parts2);

			if(parts2V.isEmpty()) return part1V.getValue().getExpr();

			Located<ConjunctDisjunctPart> firstRHS = parts2V.get(0);
			PGoTLAExpression lhs = new PGoTLABinOp(
					part1V.getLocation().combine(firstRHS.getLocation()),
					new PGoTLASymbol(firstRHS.getValue().getSymLocation().getLocation(), which),
					Collections.emptyList(),
					part1V.getValue().getExpr(),
					firstRHS.getValue().getExpr());
			for(Located<ConjunctDisjunctPart> rhs : parts2V.subList(1, parts2V.size())) {
				lhs = new PGoTLABinOp(
						lhs.getLocation().combine(rhs.getLocation()),
						new PGoTLASymbol(rhs.getValue().getSymLocation().getLocation(), which),
						Collections.emptyList(), lhs, rhs.getValue().getExpr());
			}
			return lhs;
		});

		/*return fix(self -> {
			Variable<Located<Void>> op = new Variable<>("op");
			Variable<PGoTLAExpression> expr = new Variable<>("expr");
			Variable<Located<Integer>> nextMinColumn1 = new Variable<>("nextMinColumn1");
			Variable<Located<Integer>> nextMinColumn2 = new Variable<>("nextMinColumn2");
			Variable<Located<PGoTLAExpression>> secondExpr = new Variable<>("secondExpr");
			return sequence(
					part(op, parseBuiltinToken(which, minColumn)),
					part(nextMinColumn1, access(info -> {
						Located<Void> opV = info.get(op);
						return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn()+1);
					})),
					part(nextMinColumn2, access(info -> {
						Located<Void> opV = info.get(op);
						return new Located<>(opV.getLocation(), opV.getLocation().getStartColumn());
					})),
					part(expr, recExpr.substitute(nextMinColumn1, minColumn)),
					part(secondExpr, parseOneOf(
							self
									.substitute(nextMinColumn2, minColumn)
									.map(e -> new Located<>(e.getLocation(), e)),
							nop().map(v -> new Located<>(v.getLocation(), null))
					))
			).map(seqResult -> {
				PGoTLAExpression secondExprV = seqResult.get(secondExpr).getValue();
				PGoTLAExpression exprV = seqResult.get(expr);
				if(secondExprV != null){
					Located<Void> opV = seqResult.get(op);
					return new PGoTLABinOp(
							seqResult.getLocation(),
							new PGoTLASymbol(opV.getLocation(), which),
							Collections.emptyList(), exprV, secondExprV);
				}else{
					return exprV;
				}
			});
		});*/
	}
	
	static Grammar<PGoTLAExpression> parseDisjunct(Variable<Located<Integer>> minColumn, ReferenceGrammar<PGoTLAExpression> recExpr){
		return parseConjunctOrDisjunct("\\/", minColumn, recExpr);
	}
	
	static Grammar<PGoTLAExpression> parseIfExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> ifexpr = new Variable<>("ifexpr");
		Variable<PGoTLAExpression> thenexpr = new Variable<>("thenexpr");
		Variable<PGoTLAExpression> elseexpr = new Variable<>("elseexpr");
		return sequence(
				drop(parseBuiltinToken("IF", minColumn)),
				part(ifexpr, recExpr),
				drop(parseBuiltinToken("THEN", minColumn)),
				part(thenexpr, recExpr),
				drop(parseBuiltinToken("ELSE", minColumn)),
				part(elseexpr, recExpr)
		).map(seqResult -> new PGoTLAIf(
				seqResult.getLocation(), seqResult.get(ifexpr), seqResult.get(thenexpr), seqResult.get(elseexpr)));
	}
	
	public static Grammar<PGoTLAExpression> parseCaseExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLACaseArm> firstArm = new Variable<>("firstArm");
		Variable<LocatedList<PGoTLACaseArm>> arms = new Variable<>("arms");
		Variable<Located<PGoTLAExpression>> other = new Variable<>("other");
		return sequence(
				drop(parseBuiltinToken("CASE", minColumn)),
				part(firstArm, scope(() -> {
					Variable<PGoTLAExpression> cond = new Variable<>("cond");
					Variable<PGoTLAExpression> result = new Variable<>("result");
					return sequence(
							part(cond, recExpr),
							drop(parseBuiltinToken("->", minColumn)),
							part(result, recExpr)
					).map(seqResult ->
							new PGoTLACaseArm(seqResult.getLocation(), seqResult.get(cond), seqResult.get(result)));
				})),
				part(arms, repeat(scope(() -> {
					Variable<PGoTLAExpression> cond = new Variable<>("cond");
					Variable<PGoTLAExpression> result = new Variable<>("result");
					return sequence(
							drop(parseBuiltinToken("[]", minColumn)),
							part(cond, recExpr),
							drop(parseBuiltinToken("->", minColumn)),
							part(result, recExpr)
					).map(seqResult ->
							new PGoTLACaseArm(seqResult.getLocation(), seqResult.get(cond), seqResult.get(result)));
				}))),
				part(other, parseOneOf(
						scope(() -> {
							Variable<PGoTLAExpression> other2 = new Variable<>("other2");
							return sequence(
									drop(parseBuiltinToken("[]", minColumn)),
									drop(parseBuiltinToken("OTHER", minColumn)),
									drop(parseBuiltinToken("->", minColumn)),
									part(other2, recExpr)
							).map(seqResult -> new Located<>(seqResult.getLocation(), seqResult.get(other2)));
						}),
						nop().map(v -> new Located<>(v.getLocation(), null))
				))
		).map(seqResult -> {
			LocatedList<PGoTLACaseArm> armsV = seqResult.get(arms);
			armsV.add(0, seqResult.get(firstArm));
			return new PGoTLACase(seqResult.getLocation(), armsV, seqResult.get(other).getValue());
		});
	}
	
	static Grammar<PGoTLAExpression> parseFunctionExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<PGoTLAExpression> body = new Variable<>("body");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn, recExpr), minColumn)),
				drop(parseBuiltinToken("|->", minColumn)),
				part(body, recExpr),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> new PGoTLAFunction(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(body)));
	}
	
	static Grammar<PGoTLAExpression> parseRecordSetExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLARecordSet.Field>> fields = new Variable<>("fields");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(fields, parseCommaList(scope(() -> {
					Variable<PGoTLAIdentifier> id = new Variable<>("id");
					Variable<PGoTLAExpression> set = new Variable<>("set");
					return sequence(
							part(id, parseIdentifier(minColumn)),
							drop(parseBuiltinToken(":", minColumn)),
							part(set, recExpr)
					).map(seqResult -> new PGoTLARecordSet.Field(
							seqResult.getLocation(), seqResult.get(id), seqResult.get(set)));
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
		).map(seqResult -> new PGoTLARecordSet(seqResult.getLocation(), seqResult.get(fields)));
	}
	
	static Grammar<PGoTLAExpression> parseRecordConstructorExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLARecordConstructor.Field>> fields = new Variable<>("fields");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(fields, parseCommaList(scope(() -> {
					Variable<PGoTLAIdentifier> id = new Variable<>("id");
					Variable<PGoTLAExpression> set = new Variable<>("set");
					return sequence(
							part(id, parseIdentifier(minColumn)),
							drop(parseBuiltinToken("|->", minColumn)),
							part(set, recExpr)
					).map(seqResult -> new PGoTLARecordConstructor.Field(seqResult.getLocation(), seqResult.get(id), seqResult.get(set)));
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
		).map(seqResult -> new PGoTLARecordConstructor(seqResult.getLocation(), seqResult.get(fields)));
	}
	
	static Grammar<PGoTLAExpression> parseFunctionSetExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> from = new Variable<>("from");
		Variable<PGoTLAExpression> to = new Variable<>("to");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(from, recExpr),
				drop(parseBuiltinToken("->", minColumn)),
				part(to, recExpr),
				drop(parseBuiltinToken("]", minColumn))
		).map(seqResult -> new PGoTLAFunctionSet(seqResult.getLocation(), seqResult.get(from), seqResult.get(to)));
	}
	
	static Grammar<PGoTLAExpression> parseMaybeActionExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		Variable<PGoTLAExpression> vars = new Variable<>("vars");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(expr, recExpr),
				drop(parseBuiltinToken("]_", minColumn)),
				part(vars, recExpr)
		).map(seqResult -> new PGoTLAMaybeAction(seqResult.getLocation(), seqResult.get(expr), seqResult.get(vars)));
	}
	
	static Grammar<PGoTLAExpression> parseFunctionSubstitutionExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		Variable<LocatedList<PGoTLAFunctionSubstitutionPair>> subs = new Variable<>("subs");
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(expr, recExpr),
				drop(parseBuiltinToken("EXCEPT", minColumn)),
				part(subs, parseCommaList(scope(() -> {
					Variable<LocatedList<PGoTLASubstitutionKey>> keys = new Variable<>("keys");
					Variable<PGoTLAExpression> value = new Variable<>("value");
					return sequence(
							drop(parseBuiltinToken("!", minColumn)),
							part(keys, repeatOneOrMore(
									parseOneOf(
											scope(() -> {
												Variable<PGoTLAIdentifier> id = new Variable<>("id");
												return sequence(
														drop(parseBuiltinToken(".", minColumn)),
														part(id, parseIdentifier(minColumn))
												).map(seqResult -> new PGoTLASubstitutionKey(
														seqResult.getLocation(),
														Collections.singletonList(new PGoTLAString(
																seqResult.get(id).getLocation(),
																seqResult.get(id).getId()))));
											}),
											scope(() -> {
												Variable<LocatedList<PGoTLAExpression>> indices = new Variable<>("indices");
												return sequence(
														drop(parseBuiltinToken("[", minColumn)),
														part(indices, parseCommaList(recExpr, minColumn)),
														drop(parseBuiltinToken("]", minColumn))
												).map(seqResult -> new PGoTLASubstitutionKey(
														seqResult.getLocation(),
														seqResult.get(indices)));
											})
									))),
							drop(parseBuiltinToken("=", minColumn)),
							part(value, recExpr)
					).map(seqResult -> new PGoTLAFunctionSubstitutionPair(
							seqResult.getLocation(),
							seqResult.get(keys),
							seqResult.get(value)));
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
		).map(seqResult -> new PGoTLAFunctionSubstitution(seqResult.getLocation(), seqResult.get(expr), seqResult.get(subs)));
	}
	
	static Grammar<PGoTLAExpression> parseGroupExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseBuiltinToken("(", minColumn)),
				part(expr, recExpr),
				drop(parseBuiltinToken(")", minColumn))
		).map(seqResult -> seqResult.get(expr));
	}
	
	static Grammar<PGoTLAExpression> parseQuantifiedExistentialExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseBuiltinToken("\\E", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn, recExpr), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, recExpr)
		).map(seqResult -> new PGoTLAQuantifiedExistential(
				seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}

	static Grammar<PGoTLAExpression> parseQuantifiedUniversalExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAQuantifierBound>> bounds = new Variable<>("bounds");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseBuiltinToken("\\A", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn, recExpr), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, recExpr)
		).map(seqResult -> new PGoTLAQuantifiedUniversal(
				seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<PGoTLAExpression> parseUnquantifiedExistentialExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAIdentifier>> bounds = new Variable<>("bounds");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseOneOf(
						parseBuiltinToken("\\E", minColumn),
						parseBuiltinToken("\\EE", minColumn))),
				part(bounds, parseCommaList(parseIdentifier(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, recExpr)
		).map(seqResult -> new PGoTLAExistential(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<PGoTLAExpression> parseUnquantifiedUniversalExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAIdentifier>> bounds = new Variable<>("bounds");
		Variable<PGoTLAExpression> expr = new Variable<>("expr");
		return sequence(
				drop(parseOneOf(
						parseBuiltinToken("\\A", minColumn),
						parseBuiltinToken("\\AA", minColumn))),
				part(bounds, parseCommaList(parseIdentifier(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, recExpr)
		).map(seqResult -> new PGoTLAUniversal(seqResult.getLocation(), seqResult.get(bounds), seqResult.get(expr)));
	}
	
	static Grammar<PGoTLAExpression> parseSetConstructorExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAExpression>> members = new Variable<>("members");
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(members, parseOneOf(
						parseCommaList(recExpr, minColumn),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseBuiltinToken("}", minColumn))
		).map(seqResult -> new PGoTLASetConstructor(seqResult.getLocation(), seqResult.get(members)));
	}
	
	static Grammar<PGoTLAExpression> parseSetRefinementExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAIdentifierOrTuple> ids = new Variable<>("ids");
		Variable<PGoTLAExpression> set = new Variable<>("set");
		Variable<PGoTLAExpression> condition = new Variable<>("condition");
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(ids, parseIdentifierOrTuple(minColumn)),
				drop(parseBuiltinToken("\\in", minColumn)),
				part(set, recExpr),
				drop(parseBuiltinToken(":", minColumn)),
				part(condition, recExpr),
				drop(parseBuiltinToken("}", minColumn))
		).map(seqResult -> new PGoTLASetRefinement(seqResult.getLocation(), seqResult.get(ids), seqResult.get(set), seqResult.get(condition)));
	}
	
	static Grammar<PGoTLAExpression> parseSetComprehensionExpression(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<PGoTLAExpression> generator = new Variable<>("generator");
		Variable<LocatedList<PGoTLAQuantifierBound>> sets = new Variable<>("sets");
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(generator, recExpr),
				drop(parseBuiltinToken(":", minColumn)),
				part(sets, parseCommaList(parseQuantifierBound(minColumn, recExpr), minColumn)),
				drop(parseBuiltinToken("}", minColumn))
		).map(seqResult -> new PGoTLASetComprehension(seqResult.getLocation(), seqResult.get(generator), seqResult.get(sets)));
	}
	
	static Grammar<PGoTLAExpression> parseLetExpression(Variable<Located<Integer>> minColumn, ReferenceGrammar<PGoTLAExpression> recExpr){
		Variable<LocatedList<PGoTLAUnit>> units = new Variable<>("units");
		Variable<PGoTLAExpression> body = new Variable<>("body");
		return sequence(
				drop(parseBuiltinToken("LET", minColumn)),
				part(units, repeatOneOrMore(
						parseOneOf(
								parseOperatorDefinition(minColumn, false),
								parseFunctionDefinition(minColumn, false),
								parseModuleDefinition(minColumn, false)
								))),
				drop(parseBuiltinToken("IN", minColumn)),
				part(body, recExpr)
				).map(seqResult -> new PGoTLALet(seqResult.getLocation(), seqResult.get(units), seqResult.get(body)));
	}

	static Grammar<PGoTLAExpression> parseFairnessConstraint(Variable<Located<Integer>> minColumn, Grammar<PGoTLAExpression> recExpr){
		Variable<Located<TLAFairness.Type>> type = new Variable<>("type");
		Variable<PGoTLAExpression> vars = new Variable<>("vars");
		Variable<PGoTLAExpression> expression = new Variable<>("expression");
		return sequence(
				part(type, parseOneOf(
						parseBuiltinToken("WF_", minColumn).map(v ->
								new Located<>(v.getLocation(), TLAFairness.Type.WEAK)),
						parseBuiltinToken("SF_", minColumn).map(v ->
								new Located<>(v.getLocation(), TLAFairness.Type.STRONG))
				)),
				part(vars, recExpr),
				drop(parseBuiltinToken("(", minColumn)),
				part(expression, recExpr),
				drop(parseBuiltinToken(")", minColumn))
		).map(seq -> new TLAFairness(
				seq.getLocation(), seq.get(type).getValue(), seq.get(vars), seq.get(expression)));
	}
	
	/*static Grammar<PGoTLAExpression> parseExpressionNoOperators(Variable<Located<Integer>> minColumn, ReferenceGrammar<PGoTLAExpression> recExpr){
		return EXPRESSION_NO_OPERATORS;
	}
	
	static Grammar<PGoTLAExpression> parsePrefixOperatorFromPrecedence(Variable<Located<Integer>> minColumn, int precedence, ReferenceGrammar<PGoTLAExpression> recExpr){
		List<Grammar<? extends PGoTLAExpression>> options = new ArrayList<>();
		for(String operator : PREFIX_OPERATORS) {
			if(PREFIX_OPERATORS_LOW_PRECEDENCE.get(operator) <= precedence
					&& PREFIX_OPERATORS_HI_PRECEDENCE.get(operator) >= precedence) {

				// operator - is the only operator that is both unary and binary, and can be defined as
				// both simultaneously. We special-case the unary version by renaming it.
				String opName = operator.equals("-") ? "-_" : operator;

				Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
				Variable<Located<Void>> op = new Variable<>("op");
				Variable<PGoTLAExpression> rhs = new Variable<>("rhs");
				options.add(sequence(
						part(prefix, parseInstancePrefix(minColumn, recExpr)),
						part(op, parseBuiltinToken(operator, minColumn)),
						part(rhs, OPERATORS_BY_PRECEDENCE.get(PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)/*parseExpressionFromPrecedence(
								minColumn, PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1, recExpr)//)
				).map(seqResult -> new PGoTLAUnary(
						seqResult.getLocation(),
						new PGoTLASymbol(seqResult.get(op).getLocation(), opName),
						seqResult.get(prefix),
						seqResult.get(rhs))));
			}
		}
		if(options.isEmpty()) {
			//return OPERATORS_BY_PRECEDENCE.get(precedence+1);
			return parseExpressionNoOperators(minColumn, recExpr);
		} else {
			options.add(parseExpressionNoOperators(minColumn, recExpr));
			//options.add(OPERATORS_BY_PRECEDENCE.get(precedence+1));
			return parseOneOf(options);
		}
	}*/

	private static final class InfixOperatorPart {

		private LocatedList<PGoTLAGeneralIdentifierPart> prefix;
		private Located<Void> symLocation;
		private PGoTLAExpression rhs;
		private Located<InfixOperatorPart> next;

		public InfixOperatorPart(LocatedList<PGoTLAGeneralIdentifierPart> prefix, Located<Void> symLocation,
								 PGoTLAExpression rhs, Located<InfixOperatorPart> next) {
			this.prefix = prefix;
			this.symLocation = symLocation;
			this.rhs = rhs;
			this.next = next;
		}

		public void setNext(Located<InfixOperatorPart> next) {
			this.next = next;
		}

		public LocatedList<PGoTLAGeneralIdentifierPart> getPrefix() {
			return prefix;
		}

		public Located<Void> getSymLocation() {
			return symLocation;
		}

		public PGoTLAExpression getRhs() {
			return rhs;
		}

		public PGoTLAExpression applyLhs(SourceLocation loc, PGoTLAExpression lhs, String opName) {
			if(next.getValue() != null) {
				lhs = next.getValue().applyLhs(next.getLocation(), lhs, opName);
			}
			return new PGoTLABinOp(
					lhs.getLocation().combine(loc),
					new PGoTLASymbol(symLocation.getLocation(), opName),
					prefix, lhs, rhs);
		}
	}

	private static final Map<Integer, ReferenceGrammar<PGoTLAExpression>> OPERATORS_BY_PRECEDENCE = new HashMap<>(17);
	static {
		for(int i = 1; i <= 18; ++i){
			OPERATORS_BY_PRECEDENCE.put(i, new ReferenceGrammar<PGoTLAExpression>()
					.substitute(MIN_COLUMN, MIN_COLUMN));
		}
	}
	private static final ReferenceGrammar<PGoTLAExpression> EXPRESSION_NO_OPERATORS =
			new ReferenceGrammar<PGoTLAExpression>().substitute(MIN_COLUMN, MIN_COLUMN);
	private static final ReferenceGrammar<PGoTLAExpression> EXPRESSION = OPERATORS_BY_PRECEDENCE.get(1);

	private static Grammar<PGoTLAExpression> parsePrefixOperator(int precedence) {
		List<String> operatorOptions = PREFIX_OPERATORS
				.stream()
				.filter(op ->
						precedence >= PREFIX_OPERATORS_LOW_PRECEDENCE.get(op)
								&& precedence <= PREFIX_OPERATORS_HI_PRECEDENCE.get(op))
				.collect(Collectors.toList());

		ReferenceGrammar<PGoTLAExpression> self = new ReferenceGrammar<>();

		Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");

		List<Grammar<? extends PGoTLAExpression>> options = new ArrayList<>();
		for(String operator : operatorOptions) {
			options.add(scope(() -> {
				Variable<Located<Void>> op = new Variable<>("op");
				Variable<PGoTLAExpression> expr = new Variable<>("expr");
				return sequence(
						part(op, parseBuiltinToken(operator, MIN_COLUMN)),
						part(expr, parseOneOf(
								self,
								OPERATORS_BY_PRECEDENCE.get(PREFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)
						))
				).map(seqResult -> {
					LocatedList<PGoTLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
					Located<Void> opV = seqResult.get(op);
					//System.out.println("prefix "+precedence+" "+operator);
					return new PGoTLAUnary(
							prefixV.getLocation().combine(seqResult.getLocation()),
							new PGoTLASymbol(opV.getLocation(), operator),
							seqResult.get(prefix),
							seqResult.get(expr));
				});
			}));
		}

		Variable<PGoTLAExpression> result = new Variable<>("prefixOpResult");
		Grammar<PGoTLAExpression> selfGrammar = sequence(
					part(prefix, parseInstancePrefix(MIN_COLUMN, EXPRESSION)),
					part(result, parseOneOf(options))
		).map(seqResult -> seqResult.get(result));

		self.setReferencedGrammar(selfGrammar.compile());

		return selfGrammar;
	}

	private static PGoTLAExpression buildPostfixExpression(PGoTLAExpression lhs, LocatedList<Located<PostfixOperatorPart>> parts) {
		for(Located<PostfixOperatorPart> part : parts) {
			if(part.getValue().isFunctionCall()) {
				lhs = new PGoTLAFunctionCall(
						lhs.getLocation().combine(part.getLocation()),
						lhs,
						part.getValue().getFunctionArguments());
			}else{
				lhs = new PGoTLAUnary(
						lhs.getLocation().combine(part.getLocation()),
						new PGoTLASymbol(part.getValue().getOp().getLocation(), part.getValue().getOp().getValue()),
						part.getValue().getPrefix(),
						lhs);
			}
		}
		return lhs;
	}

	private static Grammar<PGoTLAExpression> parseExpressionFromPrecedence(int precedence) {
		if(precedence > 17) {
			return EXPRESSION;
		}else{
			Variable<PGoTLAExpression> lhs = new Variable<>("lhs");
			Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");

			List<Grammar<? extends PGoTLAExpression>> afterOptions = new ArrayList<>();
			for(String operator : INFIX_OPERATORS) {
				if(INFIX_OPERATORS_LOW_PRECEDENCE.get(operator) <= precedence
						&& INFIX_OPERATORS_HI_PRECEDENCE.get(operator) >= precedence) {
					Variable<Located<Void>> op = new Variable<>("op");
					Variable<PGoTLAExpression> rhs = new Variable<>("rhs");
					Variable<LocatedList<Located<InfixOperatorPart>>> leftAssociativeParts = new Variable<>("leftAssociativeParts");
					afterOptions.add(
							sequence(
									part(op, parseInfixOperator(operator)),
									part(rhs, OPERATORS_BY_PRECEDENCE.get(INFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1)),
									part(leftAssociativeParts, INFIX_OPERATORS_LEFT_ASSOCIATIVE.contains(operator) ?
											scope(() -> {
												Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix2 = new Variable<>("prefix2");
												Variable<Located<Void>> op2 = new Variable<>("op2");
												Variable<PGoTLAExpression> rhs2 = new Variable<>("rhs2");
												return repeat(sequence(
														part(prefix2, parseInstancePrefix(MIN_COLUMN, EXPRESSION)),
														part(op2, parseInfixOperator(operator)),
														part(rhs2, OPERATORS_BY_PRECEDENCE.get(INFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1))
												).map(seqResult -> new Located<>(seqResult.getLocation(), new InfixOperatorPart(
														seqResult.get(prefix2), seqResult.get(op2), seqResult.get(rhs2), null))));
											})
											: nop().map(v -> new LocatedList<>(v.getLocation(), Collections.emptyList())))
							).map(seqResult -> {
								PGoTLAExpression lhsV = seqResult.get(lhs);
								LocatedList<PGoTLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
								Located<Void> opV = seqResult.get(op);
								lhsV = new PGoTLABinOp(
										seqResult.getLocation().combine(prefixV.getLocation()).combine(lhsV.getLocation()),
										new PGoTLASymbol(opV.getLocation(), operator),
										prefixV,
										lhsV,
										seqResult.get(rhs));

								for(Located<InfixOperatorPart> part : seqResult.get(leftAssociativeParts)) {
									lhsV = new PGoTLABinOp(
											part.getLocation().combine(lhsV.getLocation()).combine(part.getLocation()),
											new PGoTLASymbol(part.getValue().getSymLocation().getLocation(), operator),
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
				Variable<LocatedList<PGoTLAExpression>> arguments = new Variable<>("arguments");
				return sequence(
						drop(parseBuiltinToken("[", MIN_COLUMN)),
						part(arguments, parseCommaList(EXPRESSION, MIN_COLUMN)),
						drop(parseBuiltinToken("]", MIN_COLUMN))
				).map(seqResult -> new Located<>(
						seqResult.getLocation(),
						new PostfixOperatorPart(null, null, seqResult.get(arguments), true)));
			};

			Grammar<Located<PostfixOperatorPart>> postfixPartsGrammar = scope(() -> {
				Grammar<Located<PostfixOperatorPart>> operatorGrammar = scope(() -> {
					Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix2 = new Variable<>("prefix2");
					Variable<Located<String>> op2 = new Variable<>("op2");
					return sequence(
							part(prefix2, parseInstancePrefix(MIN_COLUMN, EXPRESSION)),
							part(op2, parseBuiltinTokenOneOf(relevantPostfixOperators, MIN_COLUMN))
					).map(seqResult -> new Located<>(
							seqResult.getLocation(),
							new PostfixOperatorPart(seqResult.get(prefix), seqResult.get(op2), null, false)));
				});

				return precedence <= 16 ?
						parseOneOf(operatorGrammar, functionCallGrammar.get())
						: operatorGrammar;
			});

			{

				Variable<Located<String>> op = new Variable<>("op");
				Variable<LocatedList<Located<PostfixOperatorPart>>> repeatedPostfixParts = new Variable<>("repeatedPostfixParts");
				afterOptions.add(
						sequence(
								part(op, parseBuiltinTokenOneOf(relevantPostfixOperators, MIN_COLUMN)),
								part(repeatedPostfixParts, repeat(postfixPartsGrammar))
						).map(seqResult -> {
							PGoTLAExpression lhsV = seqResult.get(lhs);
							LocatedList<PGoTLAGeneralIdentifierPart> prefixV = seqResult.get(prefix);
							Located<String> opV = seqResult.get(op);
							lhsV = new PGoTLAUnary(
									lhsV.getLocation().combine(prefixV.getLocation()).combine(opV.getLocation()),
									new PGoTLASymbol(opV.getLocation(), opV.getValue()),
									prefixV,
									lhsV);
							return buildPostfixExpression(lhsV, seqResult.get(repeatedPostfixParts));
						}));
			}

			Variable<PGoTLAExpression> extendedResult = new Variable<>("extendedResult");
			return sequence(
					part(lhs, OPERATORS_BY_PRECEDENCE.get(precedence+1)),
					parseOneOf(
							sequence(
									part(prefix, parseInstancePrefix(MIN_COLUMN, EXPRESSION)),
									part(extendedResult, parseOneOf(afterOptions))
							).map(seqResult -> new Located<>(seqResult.getLocation(), null)),
							precedence <= 16 ? parseOneOf(
									part(extendedResult, scope(() -> {
										Variable<Located<PostfixOperatorPart>> fnCall = new Variable<>("fnCall");
										Variable<LocatedList<Located<PostfixOperatorPart>>> remainingParts = new Variable<>("remainingParts");
										return sequence(
												part(fnCall, functionCallGrammar.get()),
												part(remainingParts, repeat(postfixPartsGrammar))
										).map(seqResult -> {
											Located<PostfixOperatorPart> fnCallV = seqResult.get(fnCall);
											PGoTLAExpression lhsV = seqResult.get(lhs);
											return buildPostfixExpression(
													new PGoTLAFunctionCall(
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
	}

	private static Grammar<Located<Void>> parseInfixOperator(String operator) {
		List<String> supersets = new ArrayList<>();
		for(String possibleSuperset : INFIX_OPERATORS) {
			if(possibleSuperset.length() > operator.length() && possibleSuperset.startsWith(operator)) {
				supersets.add(possibleSuperset);
			}
		}

		if(supersets.isEmpty()) return parseBuiltinToken(operator, MIN_COLUMN);

		Variable<Located<Void>> result = new Variable<>("operator");

		List<Grammar<Located<Void>>> parts = new ArrayList<>();
		parts.add(part(result, parseBuiltinToken(operator, MIN_COLUMN)));
		for(String s : supersets) {
			parts.add(reject(matchString(s.substring(operator.length()))));
		}
		return sequence(parts).map(seqResult -> seqResult.get(result));
	}

	/*static private Grammar<PGoTLAExpression> parsePostfixExpression(int precedence) {
		List<String> actualOptions = POSTFIX_OPERATORS
				.stream()
				.filter(str ->
						POSTFIX_OPERATORS_PRECEDENCE.get(str) <= precedence)
				.collect(Collectors.toList());

		Variable<PGoTLAExpression> lhs = new Variable<>("lhs");
		Variable<LocatedList<Located<PostfixOperatorPart>>> parts = new Variable<>("parts");

		Grammar<Located<PostfixOperatorPart>> partGrammar = scope(() -> {
			Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
			Variable<Located<String>> op = new Variable<>("op");
			return sequence(
					part(prefix, parseInstancePrefix(MIN_COLUMN, EXPRESSION)),
					part(op, parseBuiltinTokenOneOf(actualOptions, MIN_COLUMN))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new PostfixOperatorPart(seqResult.get(prefix), seqResult.get(op), null, false)));
		});
		Grammar<Located<PostfixOperatorPart>> functionCallGrammar = scope(() -> {
			Variable<LocatedList<PGoTLAExpression>> args = new Variable<>("args");
			return sequence(
					drop(parseBuiltinToken("[", MIN_COLUMN)),
					part(args, parseCommaList(EXPRESSION, MIN_COLUMN)),
					drop(parseBuiltinToken("]", MIN_COLUMN))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new PostfixOperatorPart(null, null, seqResult.get(args), true)));
		});

		return sequence(
				part(lhs, OPERATORS_BY_PRECEDENCE.get(precedence+1)),
				part(parts, repeat(
						precedence >= 16 ? parseOneOf(partGrammar, functionCallGrammar) : partGrammar
				))
		).map(seqResult -> {
			PGoTLAExpression lhsV = seqResult.get(lhs);
			for(Located<PostfixOperatorPart> part : seqResult.get(parts)) {
				PostfixOperatorPart p = part.getValue();
				if(p.isFunctionCall()) {
					lhsV = new PGoTLAFunctionCall(lhsV.getLocation().combine(part.getLocation()), lhsV, p.getFunctionArguments());
				}else {
					lhsV = new PGoTLAUnary(
							lhsV.getLocation().combine(part.getLocation()),
							new PGoTLASymbol(p.getOp().getLocation(), p.getOp().getValue()),
							p.getPrefix(), lhsV);
				}
			}
			//System.out.println("postfix "+precedence+" "+lhsV);
			return lhsV;
		});
	}*/

	static {
		for(int i = 1; i <= 17; ++i){
			OPERATORS_BY_PRECEDENCE.get(i).setReferencedGrammar(
					argument(MIN_COLUMN,
							parseOneOf(
									parseExpressionFromPrecedence(i),
									parsePrefixOperator(i)
							)).compile());
		}
		OPERATORS_BY_PRECEDENCE.get(18).setReferencedGrammar(argument(MIN_COLUMN, EXPRESSION_NO_OPERATORS).compile());
	}
	static {
		ReferenceGrammar<PGoTLAExpression> recExpr = EXPRESSION;
		EXPRESSION_NO_OPERATORS.setReferencedGrammar(argument(MIN_COLUMN, parseOneOf(
				parseNumber(MIN_COLUMN),
				parseString(MIN_COLUMN),
				parseBuiltinTokenOneOf(
						Arrays.asList("TRUE", "FALSE"), MIN_COLUMN)
						.map(b -> new PGoTLABool(b.getLocation(), b.getValue().equals("TRUE"))),

				parseGroupExpression(MIN_COLUMN, recExpr),
				parseTupleExpression(MIN_COLUMN, recExpr),

				parseRequiredActionExpression(MIN_COLUMN, recExpr),

				// if we find a prefix operator here, it means we hit the following situation:
				// a higher precedence prefix operator followed by a lower precedence prefix operator
				// we parse the second operator here as there is no good way to notice it "on the way down"
				parseInnerPrefixOperator(MIN_COLUMN, recExpr),

				parseOperatorCall(MIN_COLUMN, recExpr),
				// looks like an operator call but is different (WF_.*|SF_.*)
				parseFairnessConstraint(MIN_COLUMN, recExpr),

				parseConjunct(MIN_COLUMN, recExpr),
				parseDisjunct(MIN_COLUMN, recExpr),

				parseIfExpression(MIN_COLUMN, recExpr),

				parseGeneralIdentifier(MIN_COLUMN, recExpr),

				parseLetExpression(MIN_COLUMN, recExpr),

				parseCaseExpression(MIN_COLUMN, recExpr),
				// starting with [
				parseFunctionExpression(MIN_COLUMN, recExpr),
				parseRecordSetExpression(MIN_COLUMN, recExpr),
				parseRecordConstructorExpression(MIN_COLUMN, recExpr),
				parseFunctionSetExpression(MIN_COLUMN, recExpr),
				parseMaybeActionExpression(MIN_COLUMN, recExpr),
				parseFunctionSubstitutionExpression(MIN_COLUMN, recExpr),
				// starting with \E, \EE, \A, \AA
				parseQuantifiedExistentialExpression(MIN_COLUMN, recExpr),
				parseQuantifiedUniversalExpression(MIN_COLUMN, recExpr),
				parseUnquantifiedExistentialExpression(MIN_COLUMN, recExpr),
				parseUnquantifiedUniversalExpression(MIN_COLUMN, recExpr),
				//starting with {
				parseSetConstructorExpression(MIN_COLUMN, recExpr),
				parseSetRefinementExpression(MIN_COLUMN, recExpr),
				parseSetComprehensionExpression(MIN_COLUMN, recExpr)
		)).compile());
	}

	/*static Grammar<PGoTLAExpression> parseInfixOperatorFromPrecedence(Variable<Located<Integer>> minColumn, int precedence, ReferenceGrammar<PGoTLAExpression> recExpr){
		List<Grammar<? extends PGoTLAExpression>> options = new ArrayList<>();
		for(String operator : INFIX_OPERATORS) {
			if(INFIX_OPERATORS_LOW_PRECEDENCE.get(operator) <= precedence
					&& INFIX_OPERATORS_HI_PRECEDENCE.get(operator) >= precedence) {

				Variable<PGoTLAExpression> lhs = new Variable<>("lhs");
				Variable<Located<InfixOperatorPart>> parts = new Variable<>("parts");

				Function<Grammar<Located<InfixOperatorPart>>, Grammar<PGoTLAExpression>> grammarGen = partsGrammar -> sequence(
						part(lhs, parsePrefixOperatorFromPrecedence(minColumn, precedence, recExpr)),
						part(parts, partsGrammar)
				).map(seq -> {
					PGoTLAExpression lhsV = seq.get(lhs);
					Located<InfixOperatorPart> partsV = seq.get(parts);
					return partsV.getValue().applyLhs(partsV.getLocation(), lhsV, operator);
				});

				Grammar<Located<InfixOperatorPart>> partsGrammar = scope(() -> {
					Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
					Variable<Located<Void>> symLocation = new Variable<>("symLocation");
					Variable<PGoTLAExpression> rhs = new Variable<>("rhs");
					return sequence(
							part(prefix, parseInstancePrefix(minColumn, recExpr)),
							part(symLocation, parseBuiltinToken(operator, minColumn)),
							part(rhs, OPERATORS_BY_PRECEDENCE.get(INFIX_OPERATORS_HI_PRECEDENCE.get(operator)+1))
					).map(seqResult -> new Located<>(
							seqResult.getLocation(),
							new InfixOperatorPart(
									seqResult.get(prefix), seqResult.get(symLocation), seqResult.get(rhs),
									new Located<>(seqResult.getLocation(), null))));
				});

				if(INFIX_OPERATORS_LEFT_ASSOCIATIVE.contains(operator)) {
					options.add(
							grammarGen.apply(
									repeatOneOrMore(
											partsGrammar
									).map(list -> {
										Located<InfixOperatorPart> first = list.get(0);
										Located<InfixOperatorPart> current = first;
										for(Located<InfixOperatorPart> part : list.subList(1, list.size())) {
											current.getValue().setNext(part);
											current = part;
										}
										return first;
									})));
				}else{
					options.add(grammarGen.apply(partsGrammar));
				}
			}
		}
		if(options.isEmpty()) {
			return parsePrefixOperatorFromPrecedence(minColumn, precedence, recExpr);
		}else {
			options.add(parsePrefixOperatorFromPrecedence(minColumn, precedence, recExpr));
			return parseOneOf(options);
		}
	}*/

	private static final class PostfixOperatorPart {
		private LocatedList<PGoTLAGeneralIdentifierPart> prefix;
		private Located<String> op;
		private LocatedList<PGoTLAExpression> functionArguments;
		private boolean functionCall;

		public PostfixOperatorPart(LocatedList<PGoTLAGeneralIdentifierPart> prefix, Located<String> op,
								   LocatedList<PGoTLAExpression> functionArguments, boolean functionCall) {
			this.prefix = prefix;
			this.op = op;
			this.functionArguments = functionArguments;
			this.functionCall = functionCall;
		}

		public LocatedList<PGoTLAGeneralIdentifierPart> getPrefix() {
			return prefix;
		}

		public Located<String> getOp() {
			return op;
		}

		public LocatedList<PGoTLAExpression> getFunctionArguments() {
			return functionArguments;
		}

		public boolean isFunctionCall() {
			return functionCall;
		}
	}
	
	/*static Grammar<PGoTLAExpression> parsePostfixOperatorFromPrecedence(Variable<Located<Integer>> minColumn, int precedence, ReferenceGrammar<PGoTLAExpression> recExpr){

		List<String> actualOptions = POSTFIX_OPERATORS
				.stream()
				.filter(str ->
						POSTFIX_OPERATORS_PRECEDENCE.get(str) >= precedence)
				.collect(Collectors.toList());
		if(actualOptions.isEmpty()) {
			return parseInfixOperatorFromPrecedence(minColumn, precedence, recExpr);
		}

		Variable<PGoTLAExpression> lhs = new Variable<>("lhs");
		Variable<LocatedList<Located<PostfixOperatorPart>>> parts = new Variable<>("parts");

		Grammar<Located<PostfixOperatorPart>> partGrammar = scope(() -> {
			Variable<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Variable<>("prefix");
			Variable<Located<String>> op = new Variable<>("op");
			return sequence(
					part(prefix, parseInstancePrefix(minColumn, recExpr)),
					part(op, parseBuiltinTokenOneOf(actualOptions, minColumn))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new PostfixOperatorPart(seqResult.get(prefix), seqResult.get(op), null, false)));
		});
		Grammar<Located<PostfixOperatorPart>> functionCallGrammar = scope(() -> {
			Variable<LocatedList<PGoTLAExpression>> args = new Variable<>("args");
			return sequence(
					drop(parseBuiltinToken("[", minColumn)),
					part(args, parseCommaList(parseExpression(), minColumn)),
					drop(parseBuiltinToken("]", minColumn))
			).map(seqResult -> new Located<>(
					seqResult.getLocation(),
					new PostfixOperatorPart(null, null, seqResult.get(args), true)));
		});

		return sequence(
				part(lhs, parseInfixOperatorFromPrecedence(minColumn, precedence, recExpr)),
				part(parts, repeat(
						precedence <= 16 ? parseOneOf(partGrammar, functionCallGrammar) : partGrammar
				))
		).map(seqResult -> {
			PGoTLAExpression lhsV = seqResult.get(lhs);
			for(Located<PostfixOperatorPart> part : seqResult.get(parts)) {
				PostfixOperatorPart p = part.getValue();
				if(p.isFunctionCall()) {
					lhsV = new PGoTLAFunctionCall(lhsV.getLocation().combine(part.getLocation()), lhsV, p.getFunctionArguments());
				}else {
					lhsV = new PGoTLAUnary(
							lhsV.getLocation().combine(part.getLocation()),
							new PGoTLASymbol(p.getOp().getLocation(), p.getOp().getValue()),
							p.getPrefix(), lhsV);
				}
			}
			return lhsV;
		});
	}*/
	
	/*public static Grammar<PGoTLAExpression> parseExpressionFromPrecedence(Variable<Located<Integer>> minColumn, int precedence, ReferenceGrammar<PGoTLAExpression> recExpr){
		if(precedence > 17) {
			return parseExpressionNoOperators(minColumn, recExpr);
		}else {
			return parsePostfixOperatorFromPrecedence(minColumn, precedence, recExpr);
		}
	}*/
	
	/*public static Grammar<PGoTLAExpression> parseExpression(Variable<Located<Integer>> minColumn){
		return OPERATORS_BY_PRECEDENCE.get(1);
		//return fix(recExpr -> parseExpressionFromPrecedence(minColumn, 1, recExpr));
	}*/

	public static Grammar<PGoTLAExpression> parseExpression(){
		Variable<PGoTLAExpression> result = new Variable<>("result");
		return sequence(
				part(MIN_COLUMN, nop().map(v -> new Located<>(v.getLocation(), -1))),
				part(result, EXPRESSION)
		).map(seqResult -> seqResult.get(result));
	}
	
	static Grammar<PGoTLAOpDecl> parseOpDecl(Variable<Located<Integer>> minColumn){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<Located<String>> op = new Variable<>("op");
		Variable<LocatedList<Located<Void>>> args = new Variable<>("args");
		return parseOneOf(
				sequence(
						part(name, parseIdentifier(minColumn)),
						drop(parseBuiltinToken("(", minColumn)),
						part(args, parseCommaList(parseBuiltinToken("_", minColumn), minColumn)),
						drop(parseBuiltinToken(")", minColumn))
				).map(seqResult ->
						PGoTLAOpDecl.Named(seqResult.getLocation(), seqResult.get(name), seqResult.get(args).size())),
				parseIdentifier(minColumn).map(id -> PGoTLAOpDecl.Id(id.getLocation(), id)),
				sequence(
						part(op, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
						drop(parseBuiltinToken("_", minColumn))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					// operator - is the only operator that is both unary and binary, and can be defined as
					// both simultaneously. We special-case the unary version by renaming it.
					String value = opV.getValue().equals("-") ? "-_" : opV.getValue();
					return PGoTLAOpDecl.Prefix(
							seqResult.getLocation(),
							new PGoTLAIdentifier(opV.getLocation(), value));
				}),
				sequence(
						drop(parseBuiltinToken("_", minColumn)),
						part(op, parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn)),
						drop(parseBuiltinToken("_", minColumn))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					return PGoTLAOpDecl.Infix(
							seqResult.getLocation(),
							new PGoTLAIdentifier(opV.getLocation(), opV.getValue()));
				}),
				sequence(
						drop(parseBuiltinToken("_", minColumn)),
						part(op, parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn))
				).map(seqResult -> {
					Located<String> opV = seqResult.get(op);
					return PGoTLAOpDecl.Postfix(
							seqResult.getLocation(),
							new PGoTLAIdentifier(opV.getLocation(), opV.getValue()));
				})
		);
	}
	
	static Grammar<PGoTLAUnit> parseOperatorDefinition(Variable<Located<Integer>> minColumn, boolean isLocal){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<PGoTLAOpDecl>> args = new Variable<>("args");
		Variable<PGoTLAExpression> body = new Variable<>("body");
		return sequence(
				part(args, parseOneOf(
						scope(() -> {
							Variable<Located<String>> op = new Variable<>("op");
							Variable<PGoTLAIdentifier> rhs = new Variable<>("rhs");
							return sequence(
									part(op, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
									part(rhs, parseIdentifier(minColumn)),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										// operator - is the only operator that is both unary and binary, and can
										// be defined as both simultaneously. We special-case the unary version by
										// renaming it.
										String value = opV.getValue().equals("-") ? "-_" : opV.getValue();
										return new PGoTLAIdentifier(opV.getLocation(), value);
									}))
							).map(seqResult -> {
								PGoTLAIdentifier rhsV = seqResult.get(rhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Collections.singletonList(PGoTLAOpDecl.Id(rhsV.getLocation(), rhsV)));
							});
						}),
						scope(() -> {
							Variable<PGoTLAIdentifier> lhs = new Variable<>("lhs");
							Variable<Located<String>> op = new Variable<>("op");
							Variable<PGoTLAIdentifier> rhs = new Variable<>("rhs");
							return sequence(
									part(lhs, parseIdentifier(minColumn)),
									part(op, parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn)),
									part(rhs, parseIdentifier(minColumn)),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										return new PGoTLAIdentifier(opV.getLocation(), opV.getValue());
									}))
							).map(seqResult -> {
								PGoTLAIdentifier lhsV = seqResult.get(lhs);
								PGoTLAIdentifier rhsV = seqResult.get(rhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Arrays.asList(
												PGoTLAOpDecl.Id(lhsV.getLocation(), lhsV),
												PGoTLAOpDecl.Id(rhsV.getLocation(), rhsV)
										));
							});
						}),
						scope(() -> {
							Variable<PGoTLAIdentifier> lhs = new Variable<>("lhs");
							Variable<Located<String>> op = new Variable<>("op");
							return sequence(
									part(lhs, parseIdentifier(minColumn)),
									part(op, parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn)),
									part(name, access(seq -> {
										Located<String> opV = seq.get(op);
										return new PGoTLAIdentifier(opV.getLocation(), opV.getValue());
									}))
							).map(seqResult -> {
								PGoTLAIdentifier lhsV = seqResult.get(lhs);
								return new LocatedList<>(
										seqResult.getLocation(),
										Collections.singletonList(PGoTLAOpDecl.Id(
												lhsV.getLocation(), lhsV)));
							});
						}),
						scope(() -> sequence(
								part(name, parseIdentifier(minColumn)),
								part(args, parseOneOf(
										sequence(
												drop(parseBuiltinToken("(", minColumn)),
												part(args, parseCommaList(parseOpDecl(minColumn), minColumn)),
												drop(parseBuiltinToken(")", minColumn))
										).map(seqResult -> seqResult.get(args)),
										nop().map(vv -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList()))
								))
						).map(seqResult -> seqResult.get(args)))
				)),
				drop(parseBuiltinToken("==", minColumn)),
				part(body, parseExpression())
		).map(seqResult -> new PGoTLAOperatorDefinition(
				seqResult.getLocation(), seqResult.get(name), seqResult.get(args), seqResult.get(body), isLocal));
	}
	
	static Grammar<PGoTLAUnit> parseFunctionDefinition(Variable<Located<Integer>> minColumn, boolean isLocal){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<PGoTLAQuantifierBound>> args = new Variable<>("args");
		Variable<PGoTLAExpression> body = new Variable<>("body");
		return sequence(
				part(name, parseIdentifier(minColumn)),
				drop(parseBuiltinToken("[", minColumn)),
				part(args, parseCommaList(parseQuantifierBound(minColumn, parseExpression()), minColumn)),
				drop(parseBuiltinToken("]", minColumn)),
				drop(parseBuiltinToken("==", minColumn)),
				part(body, parseExpression())
		).map(seqResult -> new PGoTLAFunctionDefinition(
				seqResult.getLocation(),
				seqResult.get(name),
				new PGoTLAFunction(seqResult.getLocation(), seqResult.get(args), seqResult.get(body)),
				isLocal));
	}
	
	static Grammar<PGoTLAInstance> parseInstance(Variable<Located<Integer>> minColumn, boolean isLocal){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<PGoTLAInstance.Remapping>> remappings = new Variable<>("remappings");
		return sequence(
				drop(parseBuiltinToken("INSTANCE", minColumn)),
				part(name, parseIdentifier(minColumn)),
				part(remappings, parseOneOf(
						sequence(
								drop(parseBuiltinToken("WITH", minColumn)),
								part(remappings, parseCommaList(scope(() -> {
									Variable<PGoTLAIdentifier> from = new Variable<>("from");
									Variable<PGoTLAExpression> to = new Variable<>("to");
									return sequence(
											part(from, parseOneOf(
													parseIdentifier(minColumn),
													parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn).map(op ->
															new PGoTLAIdentifier(op.getLocation(), op.getValue())),
													parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn).map(op ->
															new PGoTLAIdentifier(op.getLocation(), op.getValue())),
													parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn).map(op ->
															new PGoTLAIdentifier(op.getLocation(), op.getValue()))
											)),
											drop(parseBuiltinToken("<-", minColumn)),
											part(to, parseExpression())
									).map(seqResult -> new PGoTLAInstance.Remapping(
											seqResult.getLocation(), seqResult.get(from), seqResult.get(to)));
								}), minColumn))
						).map(seqResult -> seqResult.get(remappings))
				))
		).map(seqResult ->
				new PGoTLAInstance(seqResult.getLocation(), seqResult.get(name), seqResult.get(remappings), isLocal));
	}
	
	static Grammar<PGoTLAUnit> parseModuleDefinition(Variable<Located<Integer>> minColumn, boolean isLocal){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<PGoTLAOpDecl>> args = new Variable<>("args");
		Variable<PGoTLAInstance> instance = new Variable<>("instance");
		return sequence(
				part(name, parseIdentifier(minColumn)),
				part(args, parseOneOf(
						sequence(
								drop(parseBuiltinToken("(", minColumn)),
								part(args, parseCommaList(parseOpDecl(minColumn), minColumn)),
								drop(parseBuiltinToken(")", minColumn))
						).map(seqResult -> seqResult.get(args)),
						nop().map(v -> new LocatedList<>(
								SourceLocation.unknown(), Collections.emptyList()))
				)),
				drop(parseBuiltinToken("==", minColumn)),
				part(instance, parseInstance(minColumn, isLocal))
		).map(seqResult ->
				new PGoTLAModuleDefinition(seqResult.getLocation(), seqResult.get(name), seqResult.get(args),
						seqResult.get(instance), isLocal));
	}
	
	static Grammar<LocatedList<PGoTLAIdentifier>> parseExtends(){
		Variable<LocatedList<PGoTLAIdentifier>> exts = new Variable<>("exts");
		return sequence(
				drop(parseBuiltinToken("EXTENDS", null)),
				part(exts, parseCommaList(parseIdentifier(null), null))
		).map(seqResult -> seqResult.get(exts));
	}
	
	static Grammar<PGoTLAUnit> parseVariableDeclaration() {
		Variable<LocatedList<PGoTLAIdentifier>> vars = new Variable<>("vars");
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("VARIABLES", "VARIABLE"), null)),
				part(vars, parseCommaList(parseIdentifier(null), null))
		).map(seqResult -> new PGoTLAVariableDeclaration(seqResult.getLocation(), seqResult.get(vars)));
	}
	
	static Grammar<PGoTLAUnit> parseConstantDeclaration(){
		Variable<LocatedList<PGoTLAOpDecl>> decls = new Variable<>("decls");
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("CONSTANTS", "CONSTANT"), null)),
				part(decls, parseCommaList(parseOpDecl(null), null))
		).map(seqResult -> new PGoTLAConstantDeclaration(seqResult.getLocation(), seqResult.get(decls)));
	}
	
	static Grammar<PGoTLAUnit> parseAssumption(){
		Variable<PGoTLAExpression> assumption = new Variable<>("assumption");
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("ASSUME", "ASSUMPTION", "AXIOM"), null)),
				part(assumption, parseExpression())
		).map(seqResult -> new PGoTLAAssumption(seqResult.getLocation(), seqResult.get(assumption)));
	}
	
	static Grammar<PGoTLAUnit> parseTheorem(){
		Variable<PGoTLAExpression> theorem = new Variable<>("theorem");
		return sequence(
				drop(parseBuiltinToken("THEOREM", null)),
				part(theorem, parseExpression())
		).map(seqResult -> new PGoTLATheorem(seqResult.getLocation(), seqResult.get(theorem)));
	}
	
	static Grammar<PGoTLAUnit> parseUnit(Grammar<PGoTLAModule> recModule){
		Variable<PGoTLAUnit> unit = new Variable<>("unit");
		Variable<Located<Integer>> minColumn = MIN_COLUMN;
		return sequence(
				/*nop().map(v -> {
					System.out.println("unit "+v);
					return v;
				}),*/
				part(minColumn, nop().map(v -> new Located<>(v.getLocation(), -1))),
				drop(parseOneOf(parse4DashesOrMore(), nop())),
				part(unit, parseOneOf(
						// all local declarations (prefixed with LOCAL)
						sequence(
								drop(parseBuiltinToken("LOCAL", minColumn)),
								part(unit, parseOneOf(
										parseInstance(minColumn, true),
										parseModuleDefinition(minColumn, true),
										parseFunctionDefinition(minColumn, true),
										parseOperatorDefinition(minColumn, true)))
						).map(seq -> seq.get(unit)),
						// all other declarations
						parseOneOf(
								parseInstance(minColumn, false),
								parseModuleDefinition(minColumn, false),
								parseFunctionDefinition(minColumn, false),
								parseOperatorDefinition(minColumn, false),
								parseVariableDeclaration(),
								parseConstantDeclaration(),
								parseAssumption(),
								parseTheorem(),
								recModule)
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
	
	static Grammar<PGoTLAModule> parseModule(Grammar<PGoTLAUnit> recUnit){
		Variable<PGoTLAIdentifier> name = new Variable<>("name");
		Variable<LocatedList<PGoTLAIdentifier>> exts = new Variable<>("exts");
		Variable<LocatedList<PGoTLAUnit>> preTranslationUnits = new Variable<>("preTranslationUnits");
		Variable<LocatedList<PGoTLAUnit>> translatedUnits = new Variable<>("translatedUnits");
		Variable<LocatedList<PGoTLAUnit>> postTranslationUnits = new Variable<>("postTranslationUnits");

		Variable<Located<Integer>> minColumn = MIN_COLUMN;
		return sequence(
				part(minColumn, nop().map(v -> new Located<>(v.getLocation(), -1))),
				drop(findModuleStart()),
				drop(parse4DashesOrMore()),
				drop(parseBuiltinToken("MODULE", minColumn)),
				part(name, parseIdentifier(minColumn)),
				drop(parse4DashesOrMore()),
				part(exts, parseOneOf(
						parseExtends(),
						nop().map(v -> new LocatedList<>(SourceLocation.unknown(), Collections.emptyList())))),
				part(preTranslationUnits, repeat(
						scope(() -> {
							Variable<PGoTLAUnit> unit = new Variable<>("unit");
							return sequence(
									// make sure we don't accidentally parse the beginning of the TLA+ translation
									reject(parseStartTranslation()),
									part(unit, recUnit)
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
									Variable<PGoTLAUnit> translatedUnit = new Variable<>("translatedUnit");
									return sequence(
													reject(parseEndTranslation()),
													part(translatedUnit, recUnit)
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
				part(postTranslationUnits, repeat(recUnit)),
				drop(parse4EqualsOrMore()),
				nop().map(v -> {
					System.out.println("COMPLETED MODULE");
					return v;
				}),
				consumeAfterModuleEnd() // consume any left-over text (that is not the beginning of another module)
		).map(seqResult ->
				new PGoTLAModule(seqResult.getLocation(), seqResult.get(name), seqResult.get(exts),
						seqResult.get(preTranslationUnits), seqResult.get(translatedUnits), seqResult.get(postTranslationUnits)));
	}

	private static final ReferenceGrammar<PGoTLAUnit> UNIT = new ReferenceGrammar<>();
	private static final ReferenceGrammar<PGoTLAModule> MODULE = new ReferenceGrammar<>();
	static {
		UNIT.setReferencedGrammar(parseUnit(MODULE).compile());
		MODULE.setReferencedGrammar(parseModule(UNIT).compile());
	}
	
	// external interfaces
	
	public static PGoTLAExpression readExpression(LexicalContext ctx) throws TLAParseException {
		return readOrExcept(ctx, parseExpression());
	}
	
	public static List<PGoTLAUnit> readUnits(LexicalContext ctx) throws TLAParseException{
		return readOrExcept(ctx, repeat(UNIT));
	}
	
	public static PGoTLAUnit readUnit(LexicalContext ctx) throws TLAParseException{
		return readOrExcept(ctx, UNIT);
	}

	public static List<PGoTLAModule> readModules(LexicalContext ctx) throws TLAParseException {
		return readOrExcept(ctx, repeatOneOrMore(MODULE));
	}
}