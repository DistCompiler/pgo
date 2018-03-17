package pgo.parser;

/**
 * 
 *  This is an LL_k recursive descent parser for an eventually-complete
 *  subset of the TLA+ language.
 * 
 *  It is written in order to match the grammar defined in Lamport's
 *  book Specifying Systems, Part IV as much as possible.
 * 
 *  Some general rules on reading/modifying this code:
 *  - all methods operator on a ListIterator<TLAToken>. The only side-effect
 * 		a method defined in this class is expected to have it moving the
 *  	iterator around the sequence of TLA+ tokens.
 *  - there are generally 2 types of helper method:
 * 		- methods matching the patter read* or expect* will unconditionally
 * 			parse a given TLA+ construct. The expected result is that
 * 			they will leave the iterator pointing to the first token after
 * 			the end of the construct. If they cannot proceed they will throw
 * 			a PGoTLAParseException containing some info on what went wrong.
 * 		
 * 			These methods will almost always return an AST node representing
 * 			the tokens they consumed, except if it is completely unambiguous
 * 			just from the function succeeding what happened.
 * 			e.g expectBuiltinToken expects one specific token, so if it
 * 			succeeded the token consumed must have been that token.
 * 		- methods matching the patter lookahead* will have one of two results:
 * 			- either they will perform identically to read* functions and
 * 				advance the iterator over tokens corresponding to the pattern
 * 				they are supposed to recognise, returning an AST node or true
 * 				to indicate success.
 * 			- or they will not advance the iterator and return either false
 * 				or null to indicate that the pattern you are asking for is not
 * 				present at this point in the input.
 * 
 * 			Similar to read* functions, if the pattern being requested is
 * 			entirely unambiguous then a simple boolean is returned to indicate
 * 			whether it was found. Otherwise, an AST node or null represents
 * 			the presence or absence of the construct.
 * 
 * 			e.g lookaheadBuiltinToken returns a boolean as there is only one
 * 		possible token to match, whereas lookaheadBuiltinTokenOneOf will return
 * 		a string indicating which of the tokens was matched.
 * 
 * 	# Operators
 * 
 * 	Since TLA+ operators come in all shapes and sizes but also follow a
 * 	fairly consistent set of rules, they are treated using a set of
 * 	static arrays and maps.
 * 
 * 	The static arrays are generally lists of operators separated by parsing
 * 	category, and the maps are used to handle operator precedence.
 * 
 *  # *_HI_PRECEDENCE and *_LO_PRECEDENCE	
 * 
 * 	    Since TLA+ operators have a range of possible precedences traditional
 * 	    precedence handling strategies fall short. We keep maps of the low
 * 	    and high bounds (inclusive) of each operator and instead of
 * 	    recursing over each operator in reverse precedence order we recurse
 * 	    directly over precedences themselves, matching any qualifying operators
 * 	    as we go.
 * 
 *  # *_LEFT_ASSOCIATIVE
 *  
 *  	Not all operators in TLA+ support associativity. It is a parse error
 *  	to accept non-bracketed repetition of non-associative operators.
 *  
 *  	So, we keep track of which operators are left-associative and only
 *  	accept repeated instances of those in these sets.
 *  
 *  # Indentation sensitivity
 * 	
 * 		TLA+ has some unusual rules surrounding chaining of the /\
 * 		and the \/ operators. Specifically, in all other cases the
 * 		language can be parsed without regard for whitespace, but
 * 		when dealing with these chains it is a parse error to unindent
 * 		part of a nested expression to a column before any leading
 * 		/\  or /\.
 * 
 * 		e.g:
 * 
 * 		The expression:
 * 		foo /\ x +
 * 		   1
 * 		
 * 		Parses as:
 * 		(foo /\ (x+)) 1
 * 
 * 		Aside from parsing pedantry, this does affect the way the parser
 * 		finds the end of subexpressions so we must implement this.
 * 
 * 		Throughout the lookahead* and expect* functions the minColumn
 * 		argument represents this constraint - if a token is found that
 * 		would otherwise match, but is at a column index lower than
 * 		minColumn, the match fails instead. This enables most of the
 * 		codebase to not have to care too much about this rule, while
 * 		consistently enforcing it.
 * 
 * 		Passing minColumn = -1 is used to disable this feature for
 * 		expressions that are not in the right hand side of /\ or \/.
 * 
 */

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import pcal.TLAToken;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOpDeclIdentifier;
import pgo.model.tla.PGoTLAOpDeclInfixOp;
import pgo.model.tla.PGoTLAOpDeclOperator;
import pgo.model.tla.PGoTLAOpDeclPostfixOp;
import pgo.model.tla.PGoTLAOpDeclPrefixOp;
import pgo.model.tla.PGoTLAOperator;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLARecord;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASet;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUniversal;
import pgo.model.tla.PGoTLAVariable;
import pgo.lexer.PGoTLATokenCategory;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAIdentifierOrTuple;
import pgo.model.tla.PGoTLAIdentifierOrTupleVisitor;
import pgo.model.tla.PGoTLAIdentifierTuple;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLANumber;

public final class TLAParser {

	private static final String[] PREFIX_OPERATORS = new String[] {
		"-",
		"~",
		"\\lnot",
		"\\neg",
		"[]",
		"<>",
		"DOMAIN",
		"ENABLED",
		"SUBSET",
		"UNCHANGED",
		"UNION",
	};
	
	private static Map<String, Integer> PREFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
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
	
	private static Map<String, Integer> PREFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
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
	
	private static final String[] INFIX_OPERATORS = new String[] {
		// infix operators (non-alpha)
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
		"\\sqsupset",
	};
	
	private static Map<String, Integer> INFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
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
	
	private static Map<String, Integer> INFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
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
	
	private static Set<String> INFIX_OPERATORS_LEFT_ASSOCIATIVE = new HashSet<>();
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
	
	private static final String[] POSTFIX_OPERATORS = new String[] {
		"^+",
		"^*",
		"^#",
		"'",
	};
	private static Map<String, Integer> POSTFIX_OPERATORS_PRECEDENCE = new HashMap<>();
	static {
		POSTFIX_OPERATORS_PRECEDENCE.put("^+", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^*", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^#", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("'", 15);
	}
	
	private static final String[] ASSUMPTION_TOKENS = new String[] {
		"ASSUME",
		"ASSUMPTION",
		"AXIOM",
	};
	
	private static final String[] CONJUNCT_DISJUNCT = new String[] {
		"\\/",
		"/\\",
	};
	
	private TLAParser(){}
	
	private static int getLineNumber(ListIterator<TLAToken> iter) {
		TLAToken tok = iter.previous();
		iter.next();
		if(tok != null) {
			return tok.source.toLocation().beginLine();
		}else {
			return -1;
		}
	}
	
	private static void expectHasNext(ListIterator<TLAToken> iter) throws PGoTLAParseException {
		if(!iter.hasNext()) {
			throw errorUnexpected(iter, "EOF");
		}
	}
	
	private static void skipNewlines(ListIterator<TLAToken> iter) {
		TLAToken tok = null;
		while(tok == null && iter.hasNext()) {
			tok = iter.next();
		}
		if(tok != null) {
			iter.previous();
		}
	}
	
	private static TLAToken readNextIgnoringNewline(ListIterator<TLAToken> iter) throws PGoTLAParseException {
		skipNewlines(iter);
		expectHasNext(iter);
		return iter.next();
	}
	
	/**
	 * This function is used to return from a lookahead. Since some
	 * lookaheads are unbounded, so it this function's ability to 
	 * go back along the input.
	 * 
	 * Users are expected to pass the result of a call to mark().
	 * 
	 * @param iter
	 * @param position the position to return to.
	 */
	private static void revert(ListIterator<TLAToken> iter, int position) {
		while(iter.nextIndex() != position) {
			iter.previous();
		}
	}
	
	/**
	 * Marks the current position that iter points to such that revert
	 * will return to that point.
	 * 
	 * @param iter
	 * @return a marker that can be passed to revert
	 */
	private static int mark(ListIterator<TLAToken> iter) {
		return iter.nextIndex();
	}
	
	private static String lookaheadIdentifier(ListIterator<TLAToken> iter, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.IDENT && tok.column > minColumn) {
			return tok.string;
		}else {
			revert(iter, initialPos);
			return null;
		}
	}
	
	private static boolean lookaheadNewline(ListIterator<TLAToken> iter) {
		int initialPos = mark(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok == null) {
			return true;
		}else {
			revert(iter, initialPos);
			return false;
		}
	}
	
	private static boolean lookaheadBuiltinToken(ListIterator<TLAToken> iter, String name, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.column > minColumn && tok.string.equals(name)) {
			return true;
		}else {
			revert(iter, initialPos);
			return false;
		}
	}
	
	private static String lookaheadBuiltinTokenOneOf(ListIterator<TLAToken> iter, String[] options, int minColumn) {
		for(String str: options) {
			if(lookaheadBuiltinToken(iter, str, minColumn)) {
				return str;
			}
		}
		return null;
	}
	
	private static String expectBuiltinTokenOneOf(ListIterator<TLAToken> iter, String[] options, int minColumn) throws PGoTLAParseException {
		for(String str: options) {
			if(lookaheadBuiltinToken(iter, str, minColumn)) {
				return str;
			}
		}
		throw errorExpectedOneOf(iter, options);
	}
	
	private static void expectBuiltinToken(ListIterator<TLAToken> iter, String name, int minColumn) throws PGoTLAParseException {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(tok.column > minColumn && !tok.string.equals(name)) {
			throw errorUnexpected(iter, tok.string);
		}
	}
	
	private static boolean lookahead4DashesOrMore(ListIterator<TLAToken> iter, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.column > minColumn && tok.string.startsWith("----")) {
			return true;
		}else {
			revert(iter, initialPos);
			return false;
		}
	}
	
	private static void expect4DashesOrMore(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(tok.column <= minColumn || tok.type != TLAToken.BUILTIN  || !tok.string.startsWith("----")) {
			throw errorExpectedOneOf(iter, "----+");
		}
	}
	
	private static boolean lookahead4EqualsOrMore(ListIterator<TLAToken> iter, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.column > minColumn && tok.string.startsWith("====")) {
			return true;
		}else {
			revert(iter, initialPos);
			return false;
		}
	}
	
	private static String expectIdentifier(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(tok.type == TLAToken.IDENT && tok.column > minColumn) {
			return tok.string;
		}else {
			throw errorExpectedOneOf(iter, "IDENTIFIER");
		}
	}
	
	private static PGoTLAParseException errorExpectedOneOf(ListIterator<TLAToken> iter, String... options) {
		int line;
		String actual;
		boolean wasEOF = !iter.hasNext();
		TLAToken tok = null;
		// do our best to find the neares token so we can provide line number info
		while(tok == null && iter.hasPrevious()) {
			tok = iter.previous();
		}
		if(tok == null) {
			while(tok == null && iter.hasNext()) {
				tok = iter.next();
			}
		}
		if(tok == null) {
			actual = wasEOF ? "EOF" : "\\n";
			line = -1;
		}else {
			actual = tok.string;
			line = tok.source.toLocation().beginLine();
		}
		return new PGoTLAParseException(line, actual, options);
	}
	
	private static PGoTLAParseException errorUnexpected(ListIterator<TLAToken> iter, String desc) {
		return new PGoTLAParseException(getLineNumber(iter), desc);
	}
	
	private static List<String> readExtends(ListIterator<TLAToken> iter) throws PGoTLAParseException{
		List<String> modules = new ArrayList<String>();
		if(lookaheadBuiltinToken(iter, "EXTENDS", -1)) {
			modules.add(expectIdentifier(iter, -1));
			while(lookaheadBuiltinToken(iter, ",", -1)) {
				modules.add(expectIdentifier(iter, -1));
			}
			return modules;
		}else {
			return null;
		}
	}
	
	private static List<String> readVariables(ListIterator<TLAToken> iter) throws PGoTLAParseException{
		List<String> variables = new ArrayList<String>();
		variables.add(expectIdentifier(iter, -1));
		while(lookaheadBuiltinToken(iter, ",", -1)) {
			variables.add(expectIdentifier(iter, -1));
		}
		return variables;
	}
	
	private static PGoTLAOpDecl readOpDecl(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		String op;
		if(lookaheadBuiltinToken(iter, "_", minColumn)) {
			op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, minColumn);
			if(op != null) {
				expectBuiltinToken(iter, "_", minColumn);
				return new PGoTLAOpDeclInfixOp(op);
			}else {
				op = expectBuiltinTokenOneOf(iter, POSTFIX_OPERATORS, minColumn);
				return new PGoTLAOpDeclPostfixOp(op);
			}
		}else if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, minColumn)) != null) {
			expectBuiltinToken(iter, "_", minColumn);
			return new PGoTLAOpDeclPrefixOp(op);
		}else {
			String id = expectIdentifier(iter, minColumn);
			if(lookaheadBuiltinToken(iter, "(", minColumn)) {
				int argCount = 0;
				do {
					expectBuiltinToken(iter, "_", minColumn);
					++argCount;
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, ")", minColumn);
				return new PGoTLAOpDeclOperator(id, argCount);
			}else {
				return new PGoTLAOpDeclIdentifier(id);
			}
		}
	}
	
	private static List<PGoTLAOpDecl> readConstants(ListIterator<TLAToken> iter) throws PGoTLAParseException{
		List<PGoTLAOpDecl> constants = new ArrayList<PGoTLAOpDecl>();
		do {
			constants.add(readOpDecl(iter, -1));
		}while(lookaheadBuiltinToken(iter, ",", -1));
		return constants;
	}
	
	private static void skipAnnotations(ListIterator<TLAToken> iter) {
		while(iter.hasNext()) {
			TLAToken tok = iter.next();
			if(tok != null && tok.type != PGoTLATokenCategory.PGO_ANNOTATION) {
				iter.previous();
				return;
			}
		}
	}
	
	private static PGoTLAExpression lookaheadString(ListIterator<TLAToken> iter, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.STRING && tok.column > minColumn) {
			return new PGoTLAString(tok.string, tok.source.toLocation().beginLine());
		}else {
			revert(iter, initialPos);
			return null;
		}
	}
	
	private static PGoTLAExpression lookaheadNumber(ListIterator<TLAToken> iter, int minColumn) {
		int initialPos = mark(iter);
		skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.NUMBER && tok.column > minColumn) {
			return new PGoTLANumber(tok.string, tok.source.toLocation().beginLine());
		}else {
			revert(iter, initialPos);
			return null;
		}
	}
	
	private static PGoTLAExpression lookaheadBoolean(ListIterator<TLAToken> iter, int minColumn) {
		if(lookaheadBuiltinToken(iter, "TRUE", minColumn)) {
			TLAToken tok = iter.previous();
			iter.next();
			return new PGoTLABool("TRUE", tok.source.toLocation().beginLine());
		}else if(lookaheadBuiltinToken(iter, "FALSE", minColumn)) {
			TLAToken tok = iter.previous();
			iter.next();
			return new PGoTLABool("FALSE", tok.source.toLocation().beginLine());
		}else {
			return null;
		}
	}
	
	private static PGoTLAExpression lookaheadPlusCalDefaultValue(ListIterator<TLAToken> iter, int minColumn) {
		if(iter.hasNext()) {
			int initialPos = mark(iter);
			TLAToken tok = iter.next();
			if(tok.column > minColumn && tok.type == PGoTLATokenCategory.PLUSCAL_DEFAULT_VALUE) {
				return new PGoTLAExpression.PGoTLADefault(tok.source.toLocation().beginLine());
			}else {
				revert(iter, initialPos);
			}
		}
		return null;
	}
	
	private static PGoTLAIdentifierOrTuple lookaheadIdentifierOrTuple(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		int lineNumber = getLineNumber(iter);
		int startIndex = mark(iter);
		String id;
		if((id = lookaheadIdentifier(iter, minColumn)) != null) {
			return new PGoTLAIdentifier(id, lineNumber);
		}
		if(lookaheadBuiltinToken(iter, "<<", minColumn)) {
			List<String> ids = new ArrayList<>();
			// empty tuples are allowed, even if they are not in the
			// official grammar
			if(!lookaheadBuiltinToken(iter, ">>", minColumn)) {
				do {
					ids.add(expectIdentifier(iter, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, ">>", minColumn);
			}
			return new PGoTLAIdentifierTuple(ids, lineNumber);
		}
		revert(iter, startIndex);
		return null;
	}
	
	private static PGoTLAIdentifierOrTuple readIdentifierOrTuple(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		PGoTLAIdentifierOrTuple result = lookaheadIdentifierOrTuple(iter, minColumn);
		if(result == null) {
			throw errorUnexpected(iter, "neither identifier nor tuple");
		}
		return result;
	}
	
	private static PGoTLAQuantifierBound lookaheadQuantifierBound(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		int startIndex = iter.nextIndex();
		PGoTLAIdentifierOrTuple id = lookaheadIdentifierOrTuple(iter, minColumn);
		if(id == null) {
			return null;
		}
		// if we got a tuple
		String singleID = id.walk(new PGoTLAIdentifierOrTupleVisitor<String>() {
			@Override
			public String visit(PGoTLAIdentifierTuple tuple) {
				return null;
			}
			
			@Override
			public String visit(PGoTLAIdentifier id) {
				return id.getId();
			}
		});
		List<String> ids = new ArrayList<>();
		if(singleID != null) {
			ids.add(singleID);
			while(lookaheadBuiltinToken(iter, ",", minColumn)) {
				singleID = lookaheadIdentifier(iter, minColumn);
				if(singleID == null) {
					revert(iter, startIndex);
					return null;
				}
				ids.add(singleID);
			}
		}else {
			ids = id.walk(new PGoTLAIdentifierOrTupleVisitor<List<String>>() {
				@Override
				public List<String> visit(PGoTLAIdentifierTuple tuple) {
					return tuple.getIdentifiers();
				}
				
				@Override
				public List<String> visit(PGoTLAIdentifier id) {
					throw new RuntimeException("unreachable");
				}
			});
		}
		
		if(lookaheadBuiltinToken(iter, "\\in", minColumn)) {
			return new PGoTLAQuantifierBound(ids, readExpression(iter));
		}
		
		revert(iter, startIndex);
		return null;
	}
	
	private static PGoTLAQuantifierBound readQuantifierBound(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		PGoTLAQuantifierBound qb = lookaheadQuantifierBound(iter, minColumn);
		if(qb == null) {
			throw errorExpectedOneOf(iter, "<QUANTIFIER_BOUND>");
		}
		return qb;
	}
	
	private static PGoTLAExpression readExpressionNoOperators(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		if(!lookaheadValidColumn(iter, minColumn)) {
			throw errorUnexpected(iter, "end of column");
		}
		PGoTLAExpression expr = null;
		expr = lookaheadNumber(iter, minColumn);
		if(expr == null) {
			expr = lookaheadString(iter, minColumn);
		}
		if(expr == null) {
			expr = lookaheadBoolean(iter, minColumn);
		}
		if(expr != null) {
			return expr;
		}
		
		if(lookaheadBuiltinToken(iter, "(", minColumn)) {
			expr = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, ")", minColumn);
			return expr;
		}
		if(lookaheadBuiltinToken(iter, "<<", minColumn)) {
			int lineNumber = getLineNumber(iter);
			List<PGoTLAExpression> exprs = new ArrayList<>();
			// if you look at the grammar, empty tuples are not allowed
			// but they exist and are used ... so we implement them
			if(!lookaheadBuiltinToken(iter, ">>", minColumn)) {
				do{
					exprs.add(readExpressionFromPrecedence(iter, 1, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
			}else {
				return new PGoTLATuple(lineNumber, exprs);
			}
			
			if(lookaheadBuiltinToken(iter, ">>_", minColumn)) {
				if(exprs.size() != 1) {
					throw errorUnexpected(iter, "multiple body clauses in operator [...]_...");
				}
				PGoTLAExpression vars = readExpressionFromPrecedence(iter, 1, minColumn);
				return new PGoTLARequiredAction(lineNumber, exprs.get(0), vars);
			}
			
			expectBuiltinToken(iter, ">>", minColumn);
			return new PGoTLATuple(lineNumber, exprs);
		}
		// TODO: support GeneralIdentifier, as well as General* forms of the operators
		String id = lookaheadIdentifier(iter, minColumn);
		if(id != null) {
			int lineNumber = getLineNumber(iter);
			if(lookaheadValidColumn(iter, minColumn)) {
				if(lookaheadBuiltinToken(iter, "(", minColumn)) {
					List<PGoTLAExpression> args = new ArrayList<>();
					do {
						args.add(readExpressionFromPrecedence(iter, 1, minColumn));
					}while(lookaheadBuiltinToken(iter, ",", minColumn));
					expectBuiltinToken(iter, ")", minColumn);
					return new PGoTLAOperatorCall(lineNumber, id, args);
				}
			}
			return new PGoTLAVariable(id, lineNumber);
		}
		
		// /\ and /\ chains
		String conjunctDisjunct = null;
		if((conjunctDisjunct = lookaheadBuiltinTokenOneOf(iter, CONJUNCT_DISJUNCT, minColumn)) != null) {
			List<PGoTLAExpression> exprs = new ArrayList<>();
			List<Integer> lineNumbers = new ArrayList<>();
			int newMinColumn = iter.previous().column;
			iter.next();
			do {
				int lineNumber = getLineNumber(iter);
				lineNumbers.add(lineNumber);
				exprs.add(readExpressionFromPrecedence(iter, 1, newMinColumn));
			}while(lookaheadNewline(iter) && lookaheadBuiltinToken(iter, conjunctDisjunct, minColumn));
			
			PGoTLAExpression lhs = exprs.get(0);
			for(int i = 1; i < exprs.size(); ++i) {
				lhs = new PGoTLABinOp(lineNumbers.get(i), conjunctDisjunct, lhs, exprs.get(0));
			}
			return lhs;
		}
		
		if(lookaheadBuiltinToken(iter, "IF", minColumn)) {
			int lineNumber = getLineNumber(iter);
			PGoTLAExpression cond = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, "THEN", minColumn);
			PGoTLAExpression tVal = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, "ELSE", minColumn);
			PGoTLAExpression fVal = readExpressionFromPrecedence(iter, 1, minColumn);
			return new PGoTLAIf(lineNumber, cond, tVal, fVal);
		}
		// seeing a "[" at this point can mean a lot of things, some of which are not supported
		// see the spec for details
		if(lookaheadBuiltinToken(iter, "[", minColumn)) {
			int lineNumber = getLineNumber(iter);
			String name = null;
			PGoTLAQuantifierBound qb = null;
			int startIndex = mark(iter);
			if((qb = lookaheadQuantifierBound(iter, minColumn)) != null) {
				List<PGoTLAQuantifierBound> bounds = new ArrayList<>();
				bounds.add(qb);
				while(lookaheadBuiltinToken(iter, ",", minColumn)) {
					bounds.add(readQuantifierBound(iter, minColumn));
				}
				expectBuiltinToken(iter, "|->", minColumn);
				PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
				return new PGoTLAFunction(bounds, body, lineNumber);
			}else if((name = lookaheadIdentifier(iter, minColumn)) != null) {
				boolean isValid = false;
				boolean isSet = false;
				String separator = null;
				if(lookaheadBuiltinToken(iter, "|->", minColumn)) {
					isSet = false;
					isValid = true;
					separator = "|->";
				}else if(lookaheadBuiltinToken(iter, ":", minColumn)) {
					isSet = true;
					isValid = true;
					separator = ":";
				}
				
				if(isValid) {
					PGoTLAExpression val = readExpressionFromPrecedence(iter, 1, minColumn);
					Map<String, List<PGoTLAExpression>> map = new HashMap<>();
					map.put(name, new ArrayList<>());
					map.get(name).add(val);
					while(lookaheadBuiltinToken(iter, ",", minColumn)) {
						name = expectIdentifier(iter, minColumn);
						expectBuiltinToken(iter, separator, minColumn);
						val = readExpressionFromPrecedence(iter, 1, minColumn);
						if(!map.containsKey(name)) {
							map.put(name, new ArrayList<>());
						}
						map.get(name).add(val);
					}
					if(isSet) {
						return new PGoTLARecordSet(map, lineNumber);
					}else {
						return new PGoTLARecord(map, lineNumber);
					}
				}else {
					// this is none of the cases that start with a name,
					// try an expression instead
					revert(iter, startIndex);
				}
			}
			
			PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
			if(lookaheadBuiltinToken(iter, "->", minColumn)) {
				PGoTLAExpression to = readExpressionFromPrecedence(iter, 1, minColumn);
				expectBuiltinToken(iter, "]", minColumn);
				return new PGoTLAFunctionSet(body, to, lineNumber);
			}else if(lookaheadBuiltinToken(iter, "]_", minColumn)) {
				PGoTLAExpression vars = readExpressionFromPrecedence(iter, 1, minColumn);
				return new PGoTLAMaybeAction(lineNumber, body, vars);
			}else {
				throw errorExpectedOneOf(iter, "->", "]_");
			}
		}
		
		if(lookaheadBuiltinToken(iter, "{", minColumn)) {
			expectValidColumn(iter, minColumn);
			if(lookaheadBuiltinToken(iter, "}", minColumn)) {
				return new PGoTLASet(new ArrayList<PGoTLAExpression>(), getLineNumber(iter));
			}
			PGoTLAIdentifierOrTuple ident;
			int lineNumber = getLineNumber(iter);
			int revertIndex = mark(iter);
			if((ident = lookaheadIdentifierOrTuple(iter, minColumn)) != null) {
				if(lookaheadBuiltinToken(iter, "\\in", minColumn)) {
					PGoTLAExpression set = readExpressionFromPrecedence(iter, 1, minColumn);
					expectBuiltinToken(iter, ":", minColumn);
					PGoTLAExpression where = readExpressionFromPrecedence(iter, 1, minColumn);
					expectBuiltinToken(iter, "}", minColumn);
					return new PGoTLASetRefinement(ident, set, where, lineNumber);
				}else {
					// rewind, we might have bitten off part of an expression
					revert(iter, revertIndex);
				}
			}
			
			PGoTLAExpression lhs = readExpressionFromPrecedence(iter, 1, minColumn);
			
			if(lookaheadBuiltinToken(iter, ":", minColumn)) {
				List<PGoTLAQuantifierBound> quantifiers = new ArrayList<>();
				do {
					quantifiers.add(readQuantifierBound(iter, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, "}", minColumn);
				return new PGoTLASetComprehension(lhs, quantifiers, lineNumber);
			}
			
			List<PGoTLAExpression> members = new ArrayList<>();
			members.add(lhs);
			if(!lookaheadBuiltinToken(iter, "}", minColumn)) {
				while(lookaheadBuiltinToken(iter, ",", minColumn)) {
					members.add(readExpressionFromPrecedence(iter, 1, minColumn));
				}
				expectBuiltinToken(iter, "}", minColumn);
			}
			return new PGoTLASet(members, lineNumber);
		}
		
		// this mess has to do with the fact that only unquantified universals
		// or existentials can start with \EE or \AA.
		// Using these flags, it's possible to share almost all code between all
		// the almost-identical cases for this parse rule.
		// Then, when we know enough about what we're parsing we throw an error
		// if the requirement is not met.
		boolean exists = false;
		boolean doubleUniversalExistential = false;
		if(lookaheadBuiltinToken(iter, "\\E", minColumn)) {
			exists = true;
			doubleUniversalExistential = false;
		}else if(lookaheadBuiltinToken(iter, "\\EE", minColumn)) {
			exists = true;
			doubleUniversalExistential = true;
		}else if(lookaheadBuiltinToken(iter, "\\AA", minColumn)) {
			doubleUniversalExistential = true;
		}
		
		if(exists || doubleUniversalExistential || lookaheadBuiltinToken(iter, "\\A", minColumn)) {
			int lineNumber = getLineNumber(iter);
			
			PGoTLAQuantifierBound qb = null;
			if((qb = lookaheadQuantifierBound(iter, minColumn)) != null) {
				
				if(doubleUniversalExistential) {
					// see above for why this error case exists
					throw errorUnexpected(iter, "quantified universal or existential starting with \\AA or \\EE");
				}
				
				List<PGoTLAQuantifierBound> qbs = new ArrayList<>();
				qbs.add(qb);
				while(lookaheadBuiltinToken(iter, ",", minColumn)) {
					qbs.add(readQuantifierBound(iter, minColumn));
				}
				expectBuiltinToken(iter, ":", minColumn);
				PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
				if(exists) {
					return new PGoTLAQuantifiedExistential(qbs, body, lineNumber);
				}else {
					return new PGoTLAQuantifiedUniversal(qbs, body, lineNumber);
				}
			}else {
				List<String> ids = new ArrayList<>();
				do {
					ids.add(expectIdentifier(iter, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, ":", minColumn);
				PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
				if(exists) {
					return new PGoTLAExistential(ids, body, lineNumber);
				}else {
					return new PGoTLAUniversal(ids, body, lineNumber);
				}
			}
		}
		
		if(lookaheadBuiltinToken(iter, "LET", minColumn)) {
			int startLine = getLineNumber(iter);
			Map<String, PGoTLAOperator> operators = new HashMap<>();
			Map<String, PGoTLAFunction> functions = new HashMap<>();
			List<PGoTLAInstance> instances = new ArrayList<>();
			do {
				if(!lookaheadOperatorFunctionOrModuleDefinition(iter, operators, functions, instances, minColumn)) {
					throw errorExpectedOneOf(iter, "OperatorDefinition", "FunctionDefinition", "ModuleDefinition");
				}
			}while(!lookaheadBuiltinToken(iter, "IN", minColumn));
			
			PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
			return new PGoTLALet(operators, functions, instances, body, startLine);
		}
		
		throw errorExpectedOneOf(iter, "[", "IF", "\\/", "/\\", "<IDENTIFIER>", "<<", "(", "<NUMBER>", "<STRING>", "<BOOLEAN>", "LET");
	}
	
	private static void expectValidColumn(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		if(!lookaheadValidColumn(iter, minColumn)) {
			throw errorUnexpected(iter, "end of column");
		}
	}

	private static boolean lookaheadValidColumn(ListIterator<TLAToken> iter, int minColumn) {
		skipNewlines(iter);
		if(!iter.hasNext()) return true;
		TLAToken tok = iter.next();
		iter.previous();
		return tok.column > minColumn;
	}
	
	private static PGoTLAExpression readExpressionFromPrecedence(ListIterator<TLAToken> iter, int precedence, int minColumn) throws PGoTLAParseException {
		if(precedence > 17) {
			return readExpressionNoOperators(iter, minColumn);
		}else {
			String op;
			PGoTLAExpression lhs = null;
			if(!lookaheadValidColumn(iter, minColumn)) {
				throw errorUnexpected(iter, "end of column");
			}
			
			if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, minColumn)) != null) {
				if(PREFIX_OPERATORS_LOW_PRECEDENCE.get(op) <= precedence && PREFIX_OPERATORS_HI_PRECEDENCE.get(op) >= precedence) {
					int lineNumber = getLineNumber(iter);
					lhs = new PGoTLAUnary(op, readExpressionFromPrecedence(iter, PREFIX_OPERATORS_HI_PRECEDENCE.get(op)+1, minColumn), lineNumber);
				}else {
					iter.previous();
					lhs = readExpressionFromPrecedence(iter, precedence + 1, minColumn);
				}
			}else {
				lhs = readExpressionFromPrecedence(iter, precedence + 1, minColumn);
			}
			
			// function application acts like an operator with precedence
			// range 16-16
			if(precedence == 16 && lookaheadBuiltinToken(iter, "[", minColumn)) {
				int lineNumber = getLineNumber(iter);
				List<PGoTLAExpression> params = new ArrayList<>();
				do {
					params.add(readExpressionFromPrecedence(iter, 1, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, "]", minColumn);
				lhs = new PGoTLAFunctionCall(lhs, params, lineNumber);
			}

			if((op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, minColumn)) != null) {
				int hiPrecedence = INFIX_OPERATORS_HI_PRECEDENCE.get(op);
				if(INFIX_OPERATORS_LOW_PRECEDENCE.get(op) <= precedence && hiPrecedence >= precedence ) {
					// this should handle precedence conflicts - we skip all conflicting precedence
					// levels when we recurse. We then allow back in repeats of the same operator
					// manually via the do-while, only if the operator we're reading allows left
					// associativity
					do {
						int lineNumber = getLineNumber(iter);
						lhs = new PGoTLABinOp(lineNumber, op, lhs, readExpressionFromPrecedence(iter, hiPrecedence+1, minColumn));
					}while(
							INFIX_OPERATORS_LEFT_ASSOCIATIVE.contains(op) &&
							lookaheadBuiltinToken(iter, op, minColumn));
				}else {
					iter.previous();
				}
			}
			if((op = lookaheadBuiltinTokenOneOf(iter, POSTFIX_OPERATORS, minColumn)) != null) {
				if(POSTFIX_OPERATORS_PRECEDENCE.get(op) == precedence) {
					lhs = new PGoTLAUnary(op, lhs, -1);
				}else {
					iter.previous();
				}
			}
			return lhs;
		}
	}
	
	public static PGoTLAExpression readExpression(ListIterator<TLAToken> iter) throws PGoTLAParseException {
		skipNewlines(iter);
		// I actually don't know if this code is necessary, if you ever see this kind of token in the wild
		// add it here
		/*PGoTLAExpression e = lookaheadPlusCalDefaultValue(iter);
		if(e != null) {
			// only reachable when parsing tokens in the context of PlusCal, where an empty expression
			// is valid and represented by this special token
			return e;
		}*/
		PGoTLAExpression e = readExpressionFromPrecedence(iter, 1, -1);
		System.out.println("Read expression "+e);
		return e;
	}
	
	private static PGoTLAModule readModule(ListIterator<TLAToken> iter) throws PGoTLAParseException {
		expect4DashesOrMore(iter, -1);
		expectBuiltinToken(iter, "MODULE", -1);
		String name = expectIdentifier(iter, -1);
		expect4DashesOrMore(iter, -1);
		List<String> exts = readExtends(iter);
		
		// accumulators for parts of the module
		List<String> variables = new ArrayList<>();
		List<PGoTLAOpDecl> constants = new ArrayList<>();
		Map<String, PGoTLAOperator> operators = new HashMap<>();
		List<PGoTLAModule> submodules = new ArrayList<>();
		Map<String, PGoTLAFunction> functions = new HashMap<>();
		List<PGoTLAInstance> instances = new ArrayList<>();
		List<PGoTLAExpression> assumptions = new ArrayList<>();
		List<PGoTLAExpression> theorems = new ArrayList<>();
		
		while(!lookahead4EqualsOrMore(iter, -1)) {
			skipAnnotations(iter);
			if(lookaheadBuiltinToken(iter, "VARIABLE", -1) || lookaheadBuiltinToken(iter, "VARIABLES", -1)) {
				variables.addAll(readVariables(iter));
			}else if(lookaheadBuiltinToken(iter, "CONSTANT", -1) || lookaheadBuiltinToken(iter, "CONSTANTS", -1)) {
				constants.addAll(readConstants(iter));
			}else if(lookaheadBuiltinTokenOneOf(iter, ASSUMPTION_TOKENS, -1) != null) {
				// assumption
				assumptions.add(readExpression(iter));
			}else if(lookaheadBuiltinToken(iter, "THEOREM", -1)) {
				// theorem
				theorems.add(readExpression(iter));
			}else if(lookahead4DashesOrMore(iter, -1)) {
				iter.previous();
				submodules.add(readModule(iter));
			}else {
				// all things that can be local (shared optional LOCAL prefix)
				if(lookaheadBuiltinToken(iter, "LOCAL", -1)) {
					// TODO: proper LOCAL support
					throw errorUnexpected(iter, "[unimplemented] LOCAL clause");
				}
				String op;
				// instance is easy to spot
				PGoTLAInstance instance = null;
				if((instance = lookaheadInstance(iter, -1)) != null) {
					instances.add(instance);
				// it's quite tricky to tell OperatorDefinition, FunctionDefinition and ModuleDefinition apart
				// so we parse them all together until we can tell what we're dealing with
				// note: factored out so we can call it from LET as well
				}else if(lookaheadOperatorFunctionOrModuleDefinition(iter, operators, functions, instances, -1)){
					// success, nothing to do here
				}else {
					throw errorExpectedOneOf(iter, "OperatorDefinition", "FunctionDefinition", "ModuleDefinition");
				}
			}
		}
		return new PGoTLAModule(name, exts, variables, constants, operators, submodules, assumptions, theorems);
	}
	
	private static boolean lookaheadOperatorFunctionOrModuleDefinition(ListIterator<TLAToken> iter, Map<String, PGoTLAOperator> operators, Map<String, PGoTLAFunction> functions, List<PGoTLAInstance> instances, int minColumn) throws PGoTLAParseException {
		String op = null;
		
		if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, minColumn)) != null) {
			// we know this is an operator definition
			String operand = expectIdentifier(iter, -1);
			String realName = op+"_";
			expectBuiltinToken(iter, "==", -1);
			List<PGoTLAOpDecl> operands = new ArrayList<>();
			operands.add(new PGoTLAOpDeclIdentifier(operand));
			if(operators.containsKey(realName)) {
				throw errorUnexpected(iter, "repeated operator definition");
			}
			operators.put(realName, new PGoTLAOperator(realName, operands, readExpression(iter)));
			return true;
		}
		
		String id = lookaheadIdentifier(iter, minColumn);
		if(id == null) {
			return false;
		}
		
		if((op = lookaheadBuiltinTokenOneOf(iter, POSTFIX_OPERATORS, minColumn)) != null) {
			System.out.println("Postfix def "+id+" "+op);
			String realName = "_"+op;
			// operator definition
			expectBuiltinToken(iter, "==", minColumn);
			List<PGoTLAOpDecl> operands = new ArrayList<>();
			operands.add(new PGoTLAOpDeclIdentifier(id));
			if(operators.containsKey(realName)) {
				throw errorUnexpected(iter, "repeated operator definition");
			}
			operators.put(realName, new PGoTLAOperator(realName, operands, readExpressionFromPrecedence(iter, 1, minColumn)));
			return true;
		}else if((op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, minColumn)) != null) {
			System.out.println("Infix def "+id+" "+op);
			String realName = "_"+op+"_";
			// operator definition
			String rhs = expectIdentifier(iter, minColumn);
			expectBuiltinToken(iter, "==", minColumn);
			List<PGoTLAOpDecl> operands = new ArrayList<>();
			operands.add(new PGoTLAOpDeclIdentifier(id));
			operands.add(new PGoTLAOpDeclIdentifier(rhs));
			if(operators.containsKey(realName)) {
				throw errorUnexpected(iter, "repeated operator definition");
			}
			operators.put(realName, new PGoTLAOperator(realName, operands, readExpressionFromPrecedence(iter, 1, minColumn)));
			return true;
		}else if(lookaheadBuiltinToken(iter, "[", minColumn)) {
			int lineNumber = getLineNumber(iter);
			List<PGoTLAQuantifierBound> bounds = new ArrayList<>();
			do {
				bounds.add(readQuantifierBound(iter, minColumn));
			}while(lookaheadBuiltinToken(iter, ",", minColumn));
			expectBuiltinToken(iter, "]", minColumn);
			expectBuiltinToken(iter, "==", minColumn);
			
			PGoTLAExpression body = readExpressionFromPrecedence(iter, 1, minColumn);
			if(functions.containsKey(id)) {
				throw errorUnexpected(iter, "repeated function definition");
			}
			functions.put(id, new PGoTLAFunction(bounds, body, lineNumber));
			return true;
		}else{
			System.out.println("Must be classic opdecls, id "+id);
			List<PGoTLAOpDecl> opdecls = new ArrayList<PGoTLAOpDecl>();
			if(lookaheadBuiltinToken(iter, "(", minColumn)) {
				do {
					opdecls.add(readOpDecl(iter, minColumn));
				}while(lookaheadBuiltinToken(iter, ",", minColumn));
				expectBuiltinToken(iter, ")", minColumn);
			}
			expectBuiltinToken(iter, "==", minColumn);
			PGoTLAInstance instance = null;
			if((instance = lookaheadInstance(iter, minColumn)) != null) {
				instance.setReferenceName(id);
				instances.add(instance);
			}else {
				operators.put(id, new PGoTLAOperator(id, opdecls, readExpressionFromPrecedence(iter, 1, minColumn)));
			}
			return true;
		}
	}
	
	private static PGoTLAInstance lookaheadInstance(ListIterator<TLAToken> iter, int minColumn) throws PGoTLAParseException {
		if(!lookaheadBuiltinToken(iter, "INSTANCE", minColumn)) {
			return null;
		}
		String name = expectIdentifier(iter, minColumn);
		
		Map<PGoTLAOpDecl, PGoTLAExpression> remappings = new HashMap<>();
		if(lookaheadBuiltinToken(iter, "WITH", minColumn)) {
			do {
				PGoTLAOpDecl id = readOpDecl(iter, minColumn);
				expectBuiltinToken(iter, "<-", minColumn);
				PGoTLAExpression val = readExpressionFromPrecedence(iter, 1, minColumn);
				if(remappings.containsKey(id)) {
					throw errorUnexpected(iter, "repeated substitution");
				}
				remappings.put(id, val);
			}while(lookaheadBuiltinToken(iter, ",", minColumn));
		}
		
		return new PGoTLAInstance(null, name, remappings);
	}

	public static List<PGoTLAModule> readModules(ListIterator<TLAToken> iter) throws PGoTLAParseException{
		List<PGoTLAModule> modules = new ArrayList<PGoTLAModule>();

		while(iter.hasNext()) {
			modules.add(readModule(iter));
			skipNewlines(iter);
		}
		
		return modules;
	}
}
