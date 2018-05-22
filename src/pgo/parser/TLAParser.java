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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAQuantifiedExistential;
import pgo.model.tla.PGoTLAQuantifiedUniversal;
import pgo.model.tla.PGoTLAQuantifierBound;
import pgo.model.tla.PGoTLARecordConstructor;
import pgo.model.tla.PGoTLARecordSet;
import pgo.model.tla.PGoTLARequiredAction;
import pgo.model.tla.PGoTLASetComprehension;
import pgo.model.tla.PGoTLASetConstructor;
import pgo.model.tla.PGoTLASetRefinement;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLASubstitutionKey;
import pgo.model.tla.PGoTLASymbol;
import pgo.model.tla.PGoTLATheorem;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAUnit;
import pgo.model.tla.PGoTLAUniversal;
import pgo.model.tla.PGoTLAVariableDeclaration;
import pgo.model.tla.PGoTLAGeneralIdentifier;
import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;
import pgo.lexer.TLAToken;
import pgo.lexer.TLATokenType;
import pgo.model.tla.PGoTLAAssumption;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLACase;
import pgo.model.tla.PGoTLACaseArm;
import pgo.model.tla.PGoTLAConstantDeclaration;
import pgo.model.tla.PGoTLAExistential;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAFunction;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAFunctionSet;
import pgo.model.tla.PGoTLAFunctionSubstitution;
import pgo.model.tla.PGoTLAFunctionSubstitutionPair;
import pgo.model.tla.PGoTLAGeneralIdentifierPart;
import pgo.model.tla.PGoTLAIdentifier;
import pgo.model.tla.PGoTLAIdentifierOrTuple;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLAInstance;
import pgo.model.tla.PGoTLALet;
import pgo.model.tla.PGoTLAMaybeAction;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAModuleDefinition;
import pgo.model.tla.PGoTLANumber;

import static pgo.parser.ParseTools.*;

public final class TLAParser {

	public static final List<String> PREFIX_OPERATORS = Arrays.asList(new String[] {
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
	});
	
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
	
	public static final List<String> INFIX_OPERATORS = Arrays.asList(new String[] {
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
	});
	
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
	
	public static final List<String> POSTFIX_OPERATORS = Arrays.asList(new String[] {
		"^+",
		"^*",
		"^#",
		"'",
	});
	public static Map<String, Integer> POSTFIX_OPERATORS_PRECEDENCE = new HashMap<>();
	static {
		POSTFIX_OPERATORS_PRECEDENCE.put("^+", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^*", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^#", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("'", 15);
	}
	
	private TLAParser(){}
	
	private static <AST extends SourceLocatable> ParseAction<LocatedList<AST>> parseCommaList(ParseAction<AST> element, int minColumn){
		return element.chain(first -> {
			return repeat(nop().chain((Void v) -> {
					Mutator<AST> ast = new Mutator<>();
					return sequence(
							drop(parseBuiltinToken(",", minColumn)),
							part(ast, element)
							).map(seqResult -> {
								return ast.getValue();
							});
			})).map((LocatedList<AST> list) -> {
				list.add(0, first);
				return list;
			});	
		});
	}
	
	private static ParseAction<PGoTLAIdentifierOrTuple> parseIdentifierTuple(int minColumn){
		Mutator<LocatedList<PGoTLAIdentifier>> ids = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(ids, parseOneOf(
						parseCommaList(parseIdentifier(minColumn), minColumn),
						nop().map(v -> new LocatedList<PGoTLAIdentifier>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseBuiltinToken(">>", minColumn))
				).map(seqResult -> {
					if(ids.getValue() != null) {
						return PGoTLAIdentifierOrTuple.Tuple(seqResult.getLocation(), ids.getValue());
					}else {
						return PGoTLAIdentifierOrTuple.Tuple(seqResult.getLocation(), Collections.emptyList());
					}
				});
	}
	
	private static ParseAction<PGoTLAIdentifierOrTuple> parseIdentifierOrTuple(int minColumn) {
		return parseOneOf(
				parseIdentifier(minColumn)
						.map(id -> PGoTLAIdentifierOrTuple.Identifier(id)),
				parseIdentifierTuple(minColumn));
	}
	
	private static ParseAction<PGoTLAQuantifierBound> parseQuantifierBound(int minColumn){
		Mutator<LocatedList<PGoTLAIdentifier>> ids = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		Mutator<PGoTLAQuantifierBound.Type> type = new Mutator<>();
		return sequence(
				part(ids, parseOneOf(
					parseIdentifierTuple(minColumn).map(tuple -> {
						type.setValue(PGoTLAQuantifierBound.Type.TUPLE);
						return new LocatedList<PGoTLAIdentifier>(tuple.getLocation(), tuple.getTuple());
					}),
					parseCommaList(parseIdentifier(minColumn), minColumn).map(list -> {
						type.setValue(PGoTLAQuantifierBound.Type.IDS);
						return list;
					})
					)),
				drop(parseBuiltinToken("\\in", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn))))
				.map(seqResult -> {
					return new PGoTLAQuantifierBound(seqResult.getLocation(), type.getValue(), ids.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<LocatedList<PGoTLAGeneralIdentifierPart>> parseInstancePrefix(int minColumn){
		return repeat(nop().chain(v -> {
			Mutator<PGoTLAIdentifier> id = new Mutator<>();
			Mutator<LocatedList<PGoTLAExpression>> args = new Mutator<>();
			return sequence(
					part(id, parseIdentifier(minColumn)),
					part(args, parseOneOf(
							nop().chain(v1 -> {
								Mutator<LocatedList<PGoTLAExpression>> innerArgs = new Mutator<>();
								return sequence(
										drop(parseBuiltinToken("(", minColumn)),
										part(innerArgs, parseCommaList(parseExpression(minColumn), minColumn)),
										drop(parseBuiltinToken(")", minColumn))
										)
										.map(seqResult -> innerArgs.getValue());
							}),
							nop().map(v1 -> new LocatedList<PGoTLAExpression>(SourceLocation.unknown(), Collections.emptyList()))
							)),
					drop(parseBuiltinToken("!", minColumn))
					)
					.map(seqResult -> {
						return new PGoTLAGeneralIdentifierPart(seqResult.getLocation(), id.getValue(), args.getValue());
					});
		}));
	}
	
	private static ParseAction<PGoTLAExpression> parseTupleExpression(int minColumn){
		Mutator<LocatedList<PGoTLAExpression>> exprs = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(exprs, parseOneOf(
						parseCommaList(nop().chain(v -> parseExpression(minColumn)), minColumn),
						nop().map(n -> new LocatedList<PGoTLAExpression>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseBuiltinToken(">>", minColumn))
				).map(seqResult -> {
					return new PGoTLATuple(seqResult.getLocation(), exprs.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseRequiredActionExpression(int minColumn){
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		Mutator<PGoTLAExpression> vars = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("<<", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken(">>_", minColumn)),
				part(vars, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLARequiredAction(seqResult.getLocation(), expr.getValue(), vars.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseInnerPrefixOperator(int minColumn){
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		Mutator<LocatedString> token = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				part(prefix, parseInstancePrefix(minColumn)),
				part(token, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAUnary(
							seqResult.getLocation(), token.getValue().getValue(),
							prefix.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseOperatorCall(int minColumn){
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		Mutator<PGoTLAIdentifier> id = new Mutator<>();
		Mutator<LocatedList<PGoTLAExpression>> args = new Mutator<>();
		return sequence(
				part(prefix, parseInstancePrefix(minColumn)),
				part(id, parseIdentifier(minColumn)),
				drop(parseBuiltinToken("(", minColumn)),
				part(args, parseCommaList(nop().chain(v -> parseExpression(minColumn)), minColumn)),
				drop(parseBuiltinToken(")", minColumn))
				).map(seqResult -> {
					return new PGoTLAOperatorCall(seqResult.getLocation(), id.getValue(),
							prefix.getValue(), args.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseGeneralIdentifier(int minColumn){
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		Mutator<PGoTLAIdentifier> id = new Mutator<>();
		return sequence(
				part(prefix, parseInstancePrefix(minColumn)),
				part(id, parseIdentifier(minColumn))
				).map(seqResult -> {
					return new PGoTLAGeneralIdentifier(seqResult.getLocation(), id.getValue(), prefix.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseConjunct(int minColumn){
		return parseBuiltinToken("/\\", minColumn).chain(str -> {
			int innerMinColumn = str.getLocation().getStartColumn();
			return parseExpression(innerMinColumn+1).chain(expr -> {
				return parseOneOf(
						parseConjunct(innerMinColumn).map(
								rhs -> new PGoTLABinOp(
										str.getLocation(),
										new PGoTLASymbol(str.getLocation(), "/\\"),
										Collections.emptyList(), expr, rhs)),
						nop().map(v -> expr));
			});
		});
	}
	
	private static ParseAction<PGoTLAExpression> parseDisjunct(int minColumn){
		return parseBuiltinToken("\\/", minColumn).chain(str -> {
			int innerMinColumn = str.getLocation().getStartColumn();
			return parseExpression(innerMinColumn+1).chain(expr -> {
				return parseOneOf(
						parseDisjunct(innerMinColumn).map(
								rhs -> new PGoTLABinOp(
										str.getLocation(),
										new PGoTLASymbol(str.getLocation(), "\\/"),
										Collections.emptyList(), expr, rhs)),
						nop().map(v -> expr));
			});
		});
	}
	
	private static ParseAction<PGoTLAExpression> parseIfExpression(int minColumn){
		Mutator<PGoTLAExpression> ifexpr = new Mutator<>();
		Mutator<PGoTLAExpression> thenexpr = new Mutator<>();
		Mutator<PGoTLAExpression> elseexpr = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("IF", minColumn)),
				part(ifexpr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("THEN", minColumn)),
				part(thenexpr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("ELSE", minColumn)),
				part(elseexpr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAIf(seqResult.getLocation(), ifexpr.getValue(), thenexpr.getValue(), elseexpr.getValue());
				});
	}
	
	public static ParseAction<PGoTLAExpression> parseCaseExpression(int minColumn){
		Mutator<PGoTLACaseArm> firstArm = new Mutator<>();
		Mutator<LocatedList<PGoTLACaseArm>> arms = new Mutator<>();
		Mutator<PGoTLAExpression> other = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("CASE", minColumn)),
				part(firstArm, nop().chain(v -> {
					Mutator<PGoTLAExpression> cond = new Mutator<>();
					Mutator<PGoTLAExpression> result = new Mutator<>();
					return sequence(
							part(cond, parseExpression(minColumn)),
							drop(parseBuiltinToken("->", minColumn)),
							part(result, parseExpression(minColumn))
							).map(seqResult -> {
								return new PGoTLACaseArm(seqResult.getLocation(), cond.getValue(), result.getValue());
							});
				})),
				part(arms, repeat(nop().chain(v -> {
					Mutator<PGoTLAExpression> cond = new Mutator<>();
					Mutator<PGoTLAExpression> result = new Mutator<>();
					return sequence(
							drop(parseBuiltinToken("[]", minColumn)),
							part(cond, parseExpression(minColumn)),
							drop(parseBuiltinToken("->", minColumn)),
							part(result, parseExpression(minColumn))
							).map(seqResult -> {
								return new PGoTLACaseArm(seqResult.getLocation(), cond.getValue(), result.getValue());
							});
				}))),
				part(other, parseOneOf(
						nop().chain(v -> {
							Mutator<PGoTLAExpression> other2 = new Mutator<>();
							return sequence(
									drop(parseBuiltinToken("[]", minColumn)),
									drop(parseBuiltinToken("OTHER", minColumn)),
									drop(parseBuiltinToken("->", minColumn)),
									part(other2, parseExpression(minColumn))
									).map(seqResult -> other2.getValue());
						}),
						nop().map(v -> null)
						))
				).map(seqResult -> {
					arms.getValue().add(0, firstArm.getValue());
					return new PGoTLACase(seqResult.getLocation(), arms.getValue(), other.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseFunctionExpression(int minColumn){
		Mutator<LocatedList<PGoTLAQuantifierBound>> bounds = new Mutator<>();
		Mutator<PGoTLAExpression> body = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn), minColumn)),
				drop(parseBuiltinToken("|->", minColumn)),
				part(body, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> {
					return new PGoTLAFunction(seqResult.getLocation(), bounds.getValue(), body.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseRecordSetExpression(int minColumn){
		Mutator<LocatedList<PGoTLARecordSet.Field>> fields = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(fields, parseCommaList(nop().chain(v -> {
					Mutator<PGoTLAIdentifier> id = new Mutator<>();
					Mutator<PGoTLAExpression> set = new Mutator<>();
					return sequence(
							part(id, parseIdentifier(minColumn)),
							drop(parseBuiltinToken(":", minColumn)),
							part(set, parseExpression(minColumn))
							).map(seqResult -> {
								return new PGoTLARecordSet.Field(seqResult.getLocation(), id.getValue(), set.getValue());
							});
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> {
					return new PGoTLARecordSet(seqResult.getLocation(), fields.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseRecordConstructorExpression(int minColumn){
		Mutator<LocatedList<PGoTLARecordConstructor.Field>> fields = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(fields, parseCommaList(nop().chain(v -> {
					Mutator<PGoTLAIdentifier> id = new Mutator<>();
					Mutator<PGoTLAExpression> set = new Mutator<>();
					return sequence(
							part(id, parseIdentifier(minColumn)),
							drop(parseBuiltinToken("|->", minColumn)),
							part(set, parseExpression(minColumn))
							).map(seqResult -> {
								return new PGoTLARecordConstructor.Field(seqResult.getLocation(), id.getValue(), set.getValue());
							});
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> {
					return new PGoTLARecordConstructor(seqResult.getLocation(), fields.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseFunctionSetExpression(int minColumn){
		Mutator<PGoTLAExpression> from = new Mutator<>();
		Mutator<PGoTLAExpression> to = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(from, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("->", minColumn)),
				part(to, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> {
					return new PGoTLAFunctionSet(seqResult.getLocation(), from.getValue(), to.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseMaybeActionExpression(int minColumn){
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		Mutator<PGoTLAExpression> vars = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("]_", minColumn)),
				part(vars, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAMaybeAction(seqResult.getLocation(), expr.getValue(), vars.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseFunctionSubstitutionExpression(int minColumn){
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		Mutator<LocatedList<PGoTLAFunctionSubstitutionPair>> subs = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("[", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("EXCEPT", minColumn)),
				part(subs, parseCommaList(nop().chain(v -> {
					Mutator<LocatedList<PGoTLASubstitutionKey>> keys = new Mutator<>();
					Mutator<PGoTLAExpression> value = new Mutator<>();
					return sequence(
							drop(parseBuiltinToken("!", minColumn)),
							part(keys, repeatOneOrMore(
									parseOneOf(
										nop().chain(vv -> {
											Mutator<PGoTLAIdentifier> id = new Mutator<>();
											return sequence(
													drop(parseBuiltinToken(".", minColumn)),
													part(id, parseIdentifier(minColumn))
													).map(seqResult -> {
														return new PGoTLASubstitutionKey(
																seqResult.getLocation(),
																Collections.singletonList(new PGoTLAString(
																		id.getValue().getLocation(),
																		id.getValue().getId())));
													});
										}),
										nop().chain(vv -> {
											Mutator<LocatedList<PGoTLAExpression>> indices = new Mutator<>();
											return sequence(
													drop(parseBuiltinToken("[", minColumn)),
													part(indices, parseCommaList(parseExpression(minColumn), minColumn)),
													drop(parseBuiltinToken("]", minColumn))
													).map(seqResult -> {
														return new PGoTLASubstitutionKey(
																seqResult.getLocation(),
																indices.getValue());
													});
										})
									))),
							drop(parseBuiltinToken("=", minColumn)),
							part(value, parseExpression(minColumn))
							).map(seqResult -> {
								return new PGoTLAFunctionSubstitutionPair(
										seqResult.getLocation(),
										keys.getValue(),
										value.getValue());
							});
				}), minColumn)),
				drop(parseBuiltinToken("]", minColumn))
				).map(seqResult -> {
					return new PGoTLAFunctionSubstitution(seqResult.getLocation(), expr.getValue(), subs.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseGroupExpression(int minColumn){
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("(", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken(")", minColumn))
				).map(seqResult -> {
					return expr.getValue();
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseQuantifiedExistentialExpression(int minColumn){
		Mutator<LocatedList<PGoTLAQuantifierBound>> bounds = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("\\E", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAQuantifiedExistential(seqResult.getLocation(), bounds.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseQuantifiedUniversalExpression(int minColumn){
		Mutator<LocatedList<PGoTLAQuantifierBound>> bounds = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("\\A", minColumn)),
				part(bounds, parseCommaList(parseQuantifierBound(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAQuantifiedUniversal(seqResult.getLocation(), bounds.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseUnquantifiedExistentialExpression(int minColumn){
		Mutator<LocatedList<PGoTLAIdentifier>> bounds = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				drop(parseOneOf(
						parseBuiltinToken("\\E", minColumn),
						parseBuiltinToken("\\EE", minColumn))),
				part(bounds, parseCommaList(parseIdentifier(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAExistential(seqResult.getLocation(), bounds.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseUnquantifiedUniversalExpression(int minColumn){
		Mutator<LocatedList<PGoTLAIdentifier>> bounds = new Mutator<>();
		Mutator<PGoTLAExpression> expr = new Mutator<>();
		return sequence(
				drop(parseOneOf(
						parseBuiltinToken("\\A", minColumn),
						parseBuiltinToken("\\AA", minColumn))),
				part(bounds, parseCommaList(parseIdentifier(minColumn), minColumn)),
				drop(parseBuiltinToken(":", minColumn)),
				part(expr, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLAUniversal(seqResult.getLocation(), bounds.getValue(), expr.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseSetConstructorExpression(int minColumn){
		Mutator<LocatedList<PGoTLAExpression>> members = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(members, parseOneOf(
						parseCommaList(nop().chain(v -> parseExpression(minColumn)), minColumn),
						nop().map(v -> new LocatedList<PGoTLAExpression>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseBuiltinToken("}", minColumn))
				).map(seqResult -> {
					return new PGoTLASetConstructor(seqResult.getLocation(), members.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseSetRefinementExpression(int minColumn){
		Mutator<PGoTLAIdentifierOrTuple> ids = new Mutator<>();
		Mutator<PGoTLAExpression> set = new Mutator<>();
		Mutator<PGoTLAExpression> condition = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(ids, parseIdentifierOrTuple(minColumn)),
				drop(parseBuiltinToken("\\in", minColumn)),
				part(set, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken(":", minColumn)),
				part(condition, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken("}", minColumn))
				).map(seqResult -> {
					return new PGoTLASetRefinement(seqResult.getLocation(), ids.getValue(), set.getValue(), condition.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseSetComprehensionExpression(int minColumn){
		Mutator<PGoTLAExpression> generator = new Mutator<>();
		Mutator<LocatedList<PGoTLAQuantifierBound>> sets = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("{", minColumn)),
				part(generator, nop().chain(v -> parseExpression(minColumn))),
				drop(parseBuiltinToken(":", minColumn)),
				part(sets, parseCommaList(parseQuantifierBound(minColumn), minColumn)),
				drop(parseBuiltinToken("}", minColumn))
				).map(seqResult -> {
					return new PGoTLASetComprehension(seqResult.getLocation(), generator.getValue(), sets.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseLetExpression(int minColumn){
		Mutator<LocatedList<PGoTLAUnit>> units = new Mutator<>();
		Mutator<PGoTLAExpression> body = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("LET", minColumn)),
				part(units, repeatOneOrMore(
						parseOneOf(
								nop().chain(v -> parseOperatorDefinition(minColumn, false)),
								nop().chain(v -> parseFunctionDefinition(minColumn, false)),
								nop().chain(v -> parseModuleDefinition(minColumn, false))
								))),
				drop(parseBuiltinToken("IN", minColumn)),
				part(body, nop().chain(v -> parseExpression(minColumn)))
				).map(seqResult -> {
					return new PGoTLALet(seqResult.getLocation(), units.getValue(), body.getValue());
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseExpressionNoOperators(int minColumn){
		return parseOneOf(
				parseNumber(minColumn).map(n -> new PGoTLANumber(n.getLocation(), n.getValue())),
				parseString(minColumn).map(s -> new PGoTLAString(s.getLocation(), s.getValue())),
				parseBuiltinTokenOneOf(
						Arrays.asList("TRUE", "FALSE"), minColumn).map(b -> {
							return new PGoTLABool(b.getLocation(), b.getValue().equals("TRUE"));
						}),
				
				parseGroupExpression(minColumn),
				parseTupleExpression(minColumn),
				
				parseRequiredActionExpression(minColumn),
				
				// if we find a prefix operator here, it means we hit the following situation:
				// a higher precedence prefix operator followed by a lower precedence prefix operator
				// we parse the second operator here as there is no good way to notice it "on the way down"
				parseInnerPrefixOperator(minColumn),
				
				parseOperatorCall(minColumn),
				
				parseGeneralIdentifier(minColumn),
				
				parseConjunct(minColumn),
				parseDisjunct(minColumn),
				
				parseIfExpression(minColumn),
				
				parseLetExpression(minColumn),
				
				parseCaseExpression(minColumn),
				// starting with [
				parseFunctionExpression(minColumn),
				parseRecordSetExpression(minColumn),
				parseRecordConstructorExpression(minColumn),
				parseFunctionSetExpression(minColumn),
				parseMaybeActionExpression(minColumn),
				parseFunctionSubstitutionExpression(minColumn),
				// starting with \E, \EE, \A, \AA
				parseQuantifiedExistentialExpression(minColumn),
				parseQuantifiedUniversalExpression(minColumn),
				parseUnquantifiedExistentialExpression(minColumn),
				parseUnquantifiedUniversalExpression(minColumn),
				//starting with {
				parseSetConstructorExpression(minColumn),
				parseSetRefinementExpression(minColumn),
				parseSetComprehensionExpression(minColumn)
				);
	}
	
	private static ParseAction<PGoTLAExpression> parsePrefixOperatorFromPrecedence(int minColumn, int precedence){
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		Mutator<LocatedString> op = new Mutator<>();
		return sequence(
				part(prefix, parseInstancePrefix(minColumn)),
				part(op, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn))
				).chain(seqResult -> {
					String opStr = op.getValue().getValue();
					if(PREFIX_OPERATORS_LOW_PRECEDENCE.get(opStr) <= precedence && PREFIX_OPERATORS_HI_PRECEDENCE.get(opStr) >= precedence) {
						return parseExpressionFromPrecedence(minColumn, PREFIX_OPERATORS_HI_PRECEDENCE.get(opStr) + 1).map(exp -> {
							return new PGoTLAUnary(seqResult.getLocation(), op.getValue().getValue(), prefix.getValue(), exp);
						});
					}else {
						return ParseAction.failure(
								ParseFailure.insufficientOperatorPrecedence(
										-1, precedence, op.getValue().getLocation()));
					}
				});
	}
	
	private static ParseAction<PGoTLAExpression> parseInfixOperatorFromPrecedence(PGoTLAExpression lhs, int minColumn, int precedence){
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		Mutator<LocatedString> op = new Mutator<>();
		
		return sequence(
				part(prefix, parseInstancePrefix(minColumn)),
				part(op, parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn))
				).chain(seqResult -> {
					String opStr = op.getValue().getValue();
					int hiPrecedence = INFIX_OPERATORS_HI_PRECEDENCE.get(opStr);
					if(INFIX_OPERATORS_LOW_PRECEDENCE.get(opStr) <= precedence && hiPrecedence >= precedence ) {
						String sameOperator = op.getValue().getValue();
						// this should handle precedence conflicts - we skip all conflicting precedence
						// levels when we recurse. We then allow back in repeats of the same operator
						// manually via the do-while, only if the operator we're reading allows left
						// associativity
						return parseExpressionFromPrecedence(minColumn, hiPrecedence).chain(rhs -> {
							Mutator<PGoTLAExpression> lhsAcc = new Mutator<>(
									new PGoTLABinOp(
											seqResult.getLocation(),
											new PGoTLASymbol(op.getValue().getLocation(), op.getValue().getValue()),
											prefix.getValue(), lhs, rhs));
							Mutator<PGoTLAExpression> repeatRHS = new Mutator<>();
							return repeat(
									sequence(
											part(prefix, parseInstancePrefix(minColumn)),
											part(op, parseBuiltinToken(sameOperator, minColumn)),
											part(repeatRHS, parseExpressionFromPrecedence(minColumn, hiPrecedence))
											).map(seqResult2 -> {
												lhsAcc.setValue(new PGoTLABinOp(
														seqResult2.getLocation(),
														new PGoTLASymbol(op.getValue().getLocation(), op.getValue().getValue()),
														prefix.getValue(),
														lhsAcc.getValue(),
														repeatRHS.getValue()
														));
												return lhsAcc.getValue();
											})
									).map(v -> lhsAcc.getValue());
						});
					}else {
						return ParseAction.failure(ParseFailure.insufficientOperatorPrecedence(
								-1, precedence, op.getValue().getLocation()));
					}
				});
	}
	
	private static ParseAction<PGoTLAExpression> parsePostfixOperatorFromPrecedence(PGoTLAExpression lhsInit, int minColumn, int precedence){
		Mutator<PGoTLAExpression> lhs = new Mutator<>(lhsInit);
		
		Mutator<LocatedList<PGoTLAExpression>> functionArguments = new Mutator<>();
		
		Mutator<LocatedString> op = new Mutator<>();
		Mutator<LocatedList<PGoTLAGeneralIdentifierPart>> prefix = new Mutator<>();
		// in order to catch high-precedence operators that were hidden by operators with a lower
		// precedence, keep trying to read operators with a higher or equal precedence until we run out
		return repeatOneOrMore(
				parseOneOf(
					sequence(
							part(prefix, parseInstancePrefix(minColumn)),
							part(op, parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn))
							).chain(seqResult -> {
								String opStr = op.getValue().getValue();
								int actualPrecedence = POSTFIX_OPERATORS_PRECEDENCE.get(opStr);
								if(actualPrecedence >= precedence) {
									lhs.setValue(
											new PGoTLAUnary(
													seqResult.getLocation(),
													opStr,
													prefix.getValue(),
													lhs.getValue()));
									return ParseAction.success(lhs.getValue());
								}else {
									return ParseAction.failure(
											ParseFailure.insufficientOperatorPrecedence(
													actualPrecedence,
													precedence,
													op.getValue().getLocation()));
								}
							}),
					sequence(
							// function application acts like a postfix operator with precedence
							// range 16-16
							drop(parseBuiltinToken("[", minColumn)),
							part(functionArguments, parseCommaList(parseExpression(minColumn), minColumn)),
							drop(parseBuiltinToken("]", minColumn))
							).chain(seqResult -> {
								if(precedence <= 16) {
									lhs.setValue(new PGoTLAFunctionCall(
											seqResult.getLocation(),
											lhs.getValue(),
											functionArguments.getValue()));
									return ParseAction.success(lhs.getValue());
								}else {
									return ParseAction.failure(
											ParseFailure.insufficientOperatorPrecedence(
													precedence,
													16,
													seqResult.getLocation()));
								}
							})
				)).map(seq -> lhs.getValue());
	}
	
	public static ParseAction<PGoTLAExpression> parseExpressionFromPrecedence(int minColumn, int precedence){	
		if(precedence > 17) {
			return parseExpressionNoOperators(minColumn);
		}else {
			return parseOneOf(
					parsePrefixOperatorFromPrecedence(minColumn, precedence),
					parseExpressionFromPrecedence(minColumn, precedence+1)
					).chain(lhs -> {
						return parseOneOf(
								parseInfixOperatorFromPrecedence(lhs, minColumn, precedence),
								nop().map(v -> lhs));
					}).chain(lhs -> {
						return parseOneOf(
								parsePostfixOperatorFromPrecedence(lhs, minColumn, precedence),
								nop().map(v -> lhs));
					});
		}
	}
	
	public static ParseAction<PGoTLAExpression> parseExpression(int minColumn){
		// TODO: PGoTLATokenCategory.PLUSCAL_DEFAULT_VALUE
		return parseExpressionFromPrecedence(minColumn, 1);
	}
	
	private static ParseAction<PGoTLAOpDecl> parseOpDecl(int minColumn){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedString> op = new Mutator<>();
		Mutator<LocatedList<LocatedString>> args = new Mutator<>();
		return parseOneOf(
				sequence(
						part(name, parseIdentifier(minColumn)),
						drop(parseBuiltinToken("(", minColumn)),
						part(args, parseCommaList(parseBuiltinToken("_", minColumn), minColumn)),
						drop(parseBuiltinToken(")", minColumn))
						).map(seqResult -> {
							return PGoTLAOpDecl.Named(seqResult.getLocation(), name.getValue(), args.getValue().size());
						}),
				parseIdentifier(minColumn).map(id -> {
					return PGoTLAOpDecl.Id(id.getLocation(), id);
				}),
				sequence(
						part(op, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
						drop(parseBuiltinToken("_", minColumn))
						).map(seqResult -> {
							return PGoTLAOpDecl.Prefix(
									seqResult.getLocation(),
									new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
						}),
				sequence(
						drop(parseBuiltinToken("_", minColumn)),
						part(op, parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn)),
						drop(parseBuiltinToken("_", minColumn))
						).map(seqResult -> {
							return PGoTLAOpDecl.Infix(
									seqResult.getLocation(),
									new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
						}),
				sequence(
						drop(parseBuiltinToken("_", minColumn)),
						part(op, parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn))
						).map(seqResult -> {
							return PGoTLAOpDecl.Postfix(
									seqResult.getLocation(),
									new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
						})
				);
	}
	
	private static ParseAction<PGoTLAUnit> parseOperatorDefinition(int minColumn, boolean isLocal){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedList<PGoTLAOpDecl>> args = new Mutator<>();
		Mutator<PGoTLAExpression> body = new Mutator<>();
		return sequence(
				part(args, parseOneOf(
						nop().chain(v -> {
							Mutator<LocatedString> op = new Mutator<>();
							Mutator<PGoTLAIdentifier> rhs = new Mutator<>();
							return sequence(
									part(op, parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn)),
									part(rhs, parseIdentifier(minColumn))
									).map(seqResult -> {
										name.setValue(new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
										SourceLocation loc = rhs.getValue().getLocation();
										return new LocatedList<PGoTLAOpDecl>(
												seqResult.getLocation(),
												Collections.singletonList(PGoTLAOpDecl.Id(loc, rhs.getValue())));
									});
						}),
						nop().chain(v -> {
							Mutator<PGoTLAIdentifier> lhs = new Mutator<>();
							Mutator<LocatedString> op = new Mutator<>();
							Mutator<PGoTLAIdentifier> rhs = new Mutator<>();
							return sequence(
									part(lhs, parseIdentifier(minColumn)),
									part(op, parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn)),
									part(rhs, parseIdentifier(minColumn))
									).map(seqResult -> {
										name.setValue(new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
										SourceLocation loc = lhs.getValue().getLocation();
										SourceLocation loc2 = rhs.getValue().getLocation();
										return new LocatedList<PGoTLAOpDecl>(
												seqResult.getLocation(),
												Arrays.asList(
														PGoTLAOpDecl.Id(loc, lhs.getValue()),
														PGoTLAOpDecl.Id(loc2, rhs.getValue())
														));
									});
						}),
						nop().chain(v -> {
							Mutator<PGoTLAIdentifier> lhs = new Mutator<>();
							Mutator<LocatedString> op = new Mutator<>();
							return sequence(
									part(lhs, parseIdentifier(minColumn)),
									part(op, parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn))
									).map(seqResult -> {
										name.setValue(new PGoTLAIdentifier(op.getValue().getLocation(), op.getValue().getValue()));
										SourceLocation loc = lhs.getValue().getLocation();
										return new LocatedList<PGoTLAOpDecl>(
												seqResult.getLocation(),
												Collections.singletonList(PGoTLAOpDecl.Id(loc, lhs.getValue())));
									});
						}),
						nop().chain(v -> {
							return sequence(
									part(name, parseIdentifier(minColumn)),
									part(args, parseOneOf(
											sequence(
													drop(parseBuiltinToken("(", minColumn)),
													part(args, parseCommaList(parseOpDecl(minColumn), minColumn)),
													drop(parseBuiltinToken(")", minColumn))
													).map(seqResult -> args.getValue()),
											nop().map(vv -> new LocatedList<PGoTLAOpDecl>(SourceLocation.unknown(), Collections.emptyList()))
											))
									).map(seqResult -> args.getValue());
						})
						)),
				drop(parseBuiltinToken("==", minColumn)),
				part(body, parseExpression(minColumn))
				).map(seqResult -> {
					return new PGoTLAOperatorDefinition(seqResult.getLocation(), name.getValue(), args.getValue(), body.getValue(), isLocal);
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseFunctionDefinition(int minColumn, boolean isLocal){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedList<PGoTLAQuantifierBound>> args = new Mutator<>();
		Mutator<PGoTLAExpression> body = new Mutator<>();
		return sequence(
				part(name, parseIdentifier(minColumn)),
				drop(parseBuiltinToken("[", minColumn)),
				part(args, parseCommaList(parseQuantifierBound(minColumn), minColumn)),
				drop(parseBuiltinToken("]", minColumn)),
				drop(parseBuiltinToken("==", minColumn)),
				part(body, parseExpression(minColumn))
				).map(seqResult -> {
					return new PGoTLAFunctionDefinition(
							seqResult.getLocation(),
							name.getValue(),
							new PGoTLAFunction(seqResult.getLocation(), args.getValue(), body.getValue()),
							isLocal);
				});
	}
	
	private static ParseAction<PGoTLAInstance> parseInstance(int minColumn, boolean isLocal){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedList<PGoTLAInstance.Remapping>> remappings = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("INSTANCE", minColumn)),
				part(name, parseIdentifier(minColumn)),
				part(remappings, parseOneOf(
						sequence(
								drop(parseBuiltinToken("WITH", minColumn)),
								part(remappings, parseCommaList(nop().chain(v -> {
									Mutator<PGoTLAIdentifier> from = new Mutator<>();
									Mutator<PGoTLAExpression> to = new Mutator<>();
									return sequence(
											part(from, parseOneOf(
													parseIdentifier(minColumn),
													parseBuiltinTokenOneOf(PREFIX_OPERATORS, minColumn).map(op -> {
														return new PGoTLAIdentifier(op.getLocation(), op.getValue());
													}),
													parseBuiltinTokenOneOf(INFIX_OPERATORS, minColumn).map(op -> {
														return new PGoTLAIdentifier(op.getLocation(), op.getValue());
													}),
													parseBuiltinTokenOneOf(POSTFIX_OPERATORS, minColumn).map(op -> {
														return new PGoTLAIdentifier(op.getLocation(), op.getValue());
													})
													)),
											drop(parseBuiltinToken("<-", minColumn)),
											part(to, parseExpression(minColumn))
											).map(seqResult -> {
												return new PGoTLAInstance.Remapping(
														seqResult.getLocation(), from.getValue(), to.getValue());
											});
								}), minColumn))
								).map(seqResult -> remappings.getValue())
						))
				).map(seqResult -> {
					return new PGoTLAInstance(seqResult.getLocation(), name.getValue(), remappings.getValue(), isLocal);
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseModuleDefinition(int minColumn, boolean isLocal){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedList<PGoTLAOpDecl>> args = new Mutator<>();
		Mutator<PGoTLAInstance> instance = new Mutator<>();
		return sequence(
				part(name, parseIdentifier(minColumn)),
				part(args, parseOneOf(
						sequence(
								drop(parseBuiltinToken("(", minColumn)),
								part(args, parseCommaList(parseOpDecl(minColumn), minColumn)),
								drop(parseBuiltinToken(")", minColumn))
								).map(seqResult -> args.getValue()),
						nop().map(v -> new LocatedList<PGoTLAOpDecl>(
								SourceLocation.unknown(), Collections.emptyList()))
						)),
				drop(parseBuiltinToken("==", minColumn)),
				part(instance, parseInstance(minColumn, isLocal))
				).map(seqResult -> {
					return new PGoTLAModuleDefinition(seqResult.getLocation(), name.getValue(), args.getValue(), instance.getValue(), isLocal);
				});
	}
	
	private static ParseAction<LocatedString> parse4DashesOrMore(){
		return parseTokenType(TLATokenType.BUILTIN, -1)
				.withContext(new WhileParsingBuiltinToken("----+"))
				.chain(s -> {
			if(s.getValue().startsWith("----")) {
				return ParseAction.success(s);
			}else {
				return ParseAction.failure(
						ParseFailure.unexpectedBuiltinToken(s, Collections.singletonList("----+")));
			}
		});
	}
	
	private static ParseAction<LocatedString> parse4EqualsOrMore(){
		return parseTokenType(TLATokenType.BUILTIN, -1)
				.withContext(new WhileParsingBuiltinToken("====+"))
				.chain(s -> {
			if(s.getValue().startsWith("====")) {
				return ParseAction.success(s);
			}else {
				return ParseAction.failure(
						ParseFailure.unexpectedBuiltinToken(s, Collections.singletonList("====+")));
			}
		});
	}
	
	private static ParseAction<LocatedList<PGoTLAIdentifier>> parseExtends(){
		Mutator<LocatedList<PGoTLAIdentifier>> exts = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("EXTENDS", -1)),
				part(exts, parseCommaList(parseIdentifier(-1), -1))
				).map(seqResult -> exts.getValue());
	}
	
	private static ParseAction<PGoTLAUnit> parseVariableDeclaration() {
		Mutator<LocatedList<PGoTLAIdentifier>> vars = new Mutator<>();
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("VARIABLE", "VARIABLES"), -1)),
				part(vars, parseCommaList(parseIdentifier(-1), -1))
				).map(seqResult -> {
					return new PGoTLAVariableDeclaration(seqResult.getLocation(), vars.getValue());
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseConstantDeclaration(){
		Mutator<LocatedList<PGoTLAOpDecl>> decls = new Mutator<>();
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("CONSTANT", "CONSTANTS"), -1)),
				part(decls, parseCommaList(parseOpDecl(-1), -1))
				).map(seqResult -> {
					return new PGoTLAConstantDeclaration(seqResult.getLocation(), decls.getValue());
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseAssumption(){
		Mutator<PGoTLAExpression> assumption = new Mutator<>();
		return sequence(
				drop(parseBuiltinTokenOneOf(Arrays.asList("ASSUME", "ASSUMPTION", "AXIOM"), -1)),
				part(assumption, parseExpression(-1))
				).map(seqResult -> {
					return new PGoTLAAssumption(seqResult.getLocation(), assumption.getValue());
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseTheorem(){
		Mutator<PGoTLAExpression> theorem = new Mutator<>();
		return sequence(
				drop(parseBuiltinToken("THEOREM", -1)),
				part(theorem, parseExpression(-1))
				).map(seqResult -> {
					return new PGoTLATheorem(seqResult.getLocation(), theorem.getValue());
				});
	}
	
	private static ParseAction<PGoTLAUnit> parseUnit(){
		return parseOneOf(
				// all units that can be declared local
				parseOneOf(
					parseBuiltinToken("LOCAL", -1).map(s -> true),
					nop().map(v -> false)
					).chain(isLocal -> {
						return parseOneOf(
								parseInstance(-1, isLocal),
								parseModuleDefinition(-1, isLocal),
								parseFunctionDefinition(-1, isLocal),
								parseOperatorDefinition(-1, isLocal)
								);
					}),
				parseVariableDeclaration(),
				parseConstantDeclaration(),
				parseAssumption(),
				parseTheorem(),
				parseModule()
				);
	}
	
	@SafeVarargs
	private static PGoTLAUnit getLastUnit(Mutator<LocatedList<PGoTLAUnit>>... mutators) {
		PGoTLAUnit lastUnit = null;
		for(Mutator<LocatedList<PGoTLAUnit>> mut : mutators) {
			if(mut.getValue() != null && !mut.getValue().isEmpty()) {
				lastUnit = mut.getValue().get(mut.getValue().size()-1);
			}
		}
		return lastUnit;
	}
	
	private static ParseAction<PGoTLAModule> parseModule(){
		Mutator<PGoTLAIdentifier> name = new Mutator<>();
		Mutator<LocatedList<PGoTLAIdentifier>> exts = new Mutator<>();
		Mutator<LocatedList<PGoTLAUnit>> preTranslationUnits = new Mutator<>();
		Mutator<LocatedList<PGoTLAUnit>> translatedUnits = new Mutator<>();
		Mutator<LocatedList<PGoTLAUnit>> postTranslationUnits = new Mutator<>();
		return sequence(
				drop(parse4DashesOrMore()),
				drop(parseBuiltinToken("MODULE", -1)),
				part(name, parseIdentifier(-1)),
				drop(parse4DashesOrMore()),
				part(exts, parseOneOf(
						parseExtends(),
						nop().map(v -> new LocatedList<PGoTLAIdentifier>(SourceLocation.unknown(), Collections.emptyList())))),
				part(preTranslationUnits, repeat(nop().chain(v -> parseUnit()))),
				part(translatedUnits, parseOneOf(
						sequence(
								drop(parseTokenType(TLATokenType.BEGIN_TRANSLATION, -1)),
								part(translatedUnits, repeat(nop().chain(v -> parseUnit()))),
								drop(parseTokenType(TLATokenType.END_TRANSLATION, -1))
								).map(seqResult -> {
									return translatedUnits.getValue();
								}),
						nop().map(v -> new LocatedList<PGoTLAUnit>(SourceLocation.unknown(), Collections.emptyList()))
						)),
				part(postTranslationUnits, repeat(nop().chain(v -> parseUnit()))),
				drop(parse4EqualsOrMore())
				)
				.withContext(() -> new AfterParsingUnit(getLastUnit(preTranslationUnits, translatedUnits, postTranslationUnits)))
				.map(seqResult -> {
					return new PGoTLAModule(seqResult.getLocation(), name.getValue(), exts.getValue(),
							preTranslationUnits.getValue(), translatedUnits.getValue(), postTranslationUnits.getValue());
				});
	}
	
	// external interfaces
	
	private static <T> T readOrExcept(ListIterator<TLAToken> iter, ParseAction<T> action) throws TLAParseException{
		ParseContext ctx = new ParseContext(iter);
		ParseResult<T> result = action.perform(ctx);
		if(result.isSuccess()) {
			return result.getSuccess();
		}else {
			throw new TLAParseException(result.getFailure());
		}
	}
	
	public static PGoTLAExpression readExpression(ListIterator<TLAToken> iter) throws TLAParseException {
		return readOrExcept(iter, parseExpression(-1));
	}
	
	public static List<PGoTLAUnit> readUnits(ListIterator<TLAToken> iter) throws TLAParseException{
		return readOrExcept(iter, repeat(parseUnit()));
	}
	
	public static PGoTLAUnit readUnit(ListIterator<TLAToken> iter) throws TLAParseException{
		return readOrExcept(iter, parseUnit());
	}

	public static List<PGoTLAModule> readModules(ListIterator<TLAToken> iter) throws TLAParseException {
		return readOrExcept(iter, repeatOneOrMore(parseModule()));
	}
}
