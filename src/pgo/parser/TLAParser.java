package pgo.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import pcal.TLAToken;
import pgo.model.tla.PGoTLAOpDecl;
import pgo.model.tla.PGoTLAOpDeclIdentifier;
import pgo.model.tla.PGoTLAOpDeclInfixOp;
import pgo.model.tla.PGoTLAOpDeclOperator;
import pgo.model.tla.PGoTLAOpDeclPostfixOp;
import pgo.model.tla.PGoTLAOpDeclPrefixOp;
import pgo.model.tla.PGoTLAOperator;
import pgo.model.tla.PGoTLAOperatorCall;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLATuple;
import pgo.model.tla.PGoTLAUnary;
import pgo.model.tla.PGoTLAVariable;
import pgo.model.tla.PGoTLABinOp;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAIf;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLANumber;

public class TLAParser {
	private List<TLAToken> tokens;
	
	static String MODULE = "MODULE";
	static String EXTENDS = "EXTENDS";
	static String COMMA = ",";
	static String UNDERSCORE = "_";
	static String[] PREFIX_OPERATORS = new String[] {
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
	
	static Map<String, Integer> PREFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
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
	
	static Map<String, Integer> PREFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
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
	
	static String[] INFIX_OPERATORS = new String[] {
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
	
	static Map<String, Integer> INFIX_OPERATORS_LOW_PRECEDENCE = new HashMap<>();
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
	
	static Map<String, Integer> INFIX_OPERATORS_HI_PRECEDENCE = new HashMap<>();
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
	
	static String[] POSTFIX_OPERATORS = new String[] {
		"^+",
		"^*",
		"^#",
		"'",
	};
	static Map<String, Integer> POSTFIX_OPERATORS_PRECEDENCE = new HashMap<>();
	static {
		POSTFIX_OPERATORS_PRECEDENCE.put("^+", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^*", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("^#", 15);
		POSTFIX_OPERATORS_PRECEDENCE.put("'", 15);
	}
	
	static String[] ASSUMPTION_TOKENS = new String[] {
		"ASSUME",
		"ASSUMPTION",
		"AXIOM",
	};
	
	public TLAParser(List<TLAToken> tokens){
		this.tokens = tokens;
	}
	
	private void expectHasNext(ListIterator<TLAToken> iter) {
		if(!iter.hasNext()) {
			throw new RuntimeException("Unexpected end of file.");
		}
	}
	
	private void skipNewlines(ListIterator<TLAToken> iter) {
		TLAToken tok = null;
		while(tok == null && iter.hasNext()) {
			tok = iter.next();
		}
		if(tok != null) {
			iter.previous();
		}
	}
	
	private TLAToken readNextIgnoringNewline(ListIterator<TLAToken> iter) {
		skipNewlines(iter);
		expectHasNext(iter);
		return iter.next();
	}
	
	private String lookaheadIdentifier(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.IDENT) {
			return tok.string;
		}else {
			iter.previous();
			return null;
		}
	}
	
	private boolean lookaheadNewline(ListIterator<TLAToken> iter) {
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok == null) {
			return true;
		}else {
			iter.previous();
			return false;
		}
	}
	
	private boolean lookaheadBuiltinToken(ListIterator<TLAToken> iter, String name, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.string.equals(name)) {
			return true;
		}else {
			iter.previous();
			return false;
		}
	}
	
	private String lookaheadBuiltinTokenOneOf(ListIterator<TLAToken> iter, String[] options, boolean skipNewlines) {
		for(String str: options) {
			if(lookaheadBuiltinToken(iter, str, skipNewlines)) {
				return str;
			}
		}
		return null;
	}
	
	private String expectBuiltinTokenOneOf(ListIterator<TLAToken> iter, String[] options) {
		for(String str: options) {
			if(lookaheadBuiltinToken(iter, str, true)) {
				return str;
			}
		}
		String actual = iter.hasNext() ? iter.next().toString() : "EOF";
		throw new RuntimeException("Expected one of tokens ["+String.join(", ", options)+"], got "+actual);
	}
	
	private void expectBuiltinToken(ListIterator<TLAToken> iter, String name) {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(!tok.string.equals(name)) {
			throw new RuntimeException("Unexpected token "+tok+", expected "+name);
		}
	}
	
	private boolean lookahead4DashesOrMore(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.string.startsWith("----")) {
			return true;
		}else {
			iter.previous();
			return false;
		}
	}
	
	private void expect4DashesOrMore(ListIterator<TLAToken> iter) {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(tok.type != TLAToken.BUILTIN || !tok.string.startsWith("----")) {
			throw new RuntimeException("Unexpected token "+tok+", expected ----+");
		}
	}
	
	private boolean lookahead4EqualsOrMore(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return false;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.BUILTIN && tok.string.startsWith("====")) {
			return true;
		}else {
			iter.previous();
			return false;
		}
	}
	
	private String expectIdentifier(ListIterator<TLAToken> iter) {
		TLAToken tok = readNextIgnoringNewline(iter);
		if(tok.type == TLAToken.IDENT) {
			return tok.string;
		}else {
			throw new RuntimeException("Unexpected token "+tok+", expected identifier");
		}
	}
	
	private List<String> readExtends(ListIterator<TLAToken> iter){
		List<String> modules = new ArrayList<String>();
		if(lookaheadBuiltinToken(iter, EXTENDS, true)) {
			modules.add(expectIdentifier(iter));
			while(lookaheadBuiltinToken(iter, COMMA, true)) {
				modules.add(expectIdentifier(iter));
			}
			return modules;
		}else {
			return null;
		}
	}
	
	private List<String> readVariables(ListIterator<TLAToken> iter){
		List<String> variables = new ArrayList<String>();
		variables.add(expectIdentifier(iter));
		while(lookaheadBuiltinToken(iter, COMMA, true)) {
			variables.add(expectIdentifier(iter));
		}
		return variables;
	}
	
	private PGoTLAOpDecl readOpDecl(ListIterator<TLAToken> iter) {
		String op;
		if(lookaheadBuiltinToken(iter, UNDERSCORE, true)) {
			op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, true);
			if(op != null) {
				expectBuiltinToken(iter, UNDERSCORE);
				return new PGoTLAOpDeclInfixOp(op);
			}else {
				op = expectBuiltinTokenOneOf(iter, POSTFIX_OPERATORS);
				return new PGoTLAOpDeclPostfixOp(op);
			}
		}else if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, true)) != null) {
			expectBuiltinToken(iter, UNDERSCORE);
			return new PGoTLAOpDeclPrefixOp(op);
		}else {
			String id = expectIdentifier(iter);
			if(lookaheadBuiltinToken(iter, "(", true)) {
				int argCount = 0;
				do {
					expectBuiltinToken(iter, UNDERSCORE);
					++argCount;
				}while(lookaheadBuiltinToken(iter, COMMA, true));
				expectBuiltinToken(iter, ")");
				return new PGoTLAOpDeclOperator(id, argCount);
			}else {
				return new PGoTLAOpDeclIdentifier(id);
			}
		}
	}
	
	private List<PGoTLAOpDecl> readConstants(ListIterator<TLAToken> iter){
		List<PGoTLAOpDecl> constants = new ArrayList<PGoTLAOpDecl>();
		do {
			constants.add(readOpDecl(iter));
		}while(lookaheadBuiltinToken(iter, COMMA, true));
		return constants;
	}
	
	private void skipAnnotations(ListIterator<TLAToken> iter) {
		while(iter.hasNext()) {
			TLAToken tok = iter.next();
			if(tok == null || tok.type != 0xFFFF) {
				iter.previous();
				return;
			}
		}
	}
	
	private PGoTLAExpression lookaheadString(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.STRING) {
			return new PGoTLAString(tok.string, tok.source.toLocation().beginLine());
		}else {
			iter.previous();
			return null;
		}
	}
	
	private PGoTLAExpression lookaheadNumber(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(skipNewlines) skipNewlines(iter);
		if(!iter.hasNext()) return null;
		TLAToken tok = iter.next();
		if(tok.type == TLAToken.NUMBER) {
			return new PGoTLANumber(tok.string, tok.source.toLocation().beginLine());
		}else {
			iter.previous();
			return null;
		}
	}
	
	private PGoTLAExpression lookaheadBoolean(ListIterator<TLAToken> iter, boolean skipNewlines) {
		if(lookaheadBuiltinToken(iter, "TRUE", skipNewlines)) {
			TLAToken tok = iter.previous();
			iter.next();
			return new PGoTLABool("TRUE", tok.source.toLocation().beginLine());
		}else if(lookaheadBuiltinToken(iter, "FALSE", skipNewlines)) {
			TLAToken tok = iter.previous();
			iter.next();
			return new PGoTLABool("FALSE", tok.source.toLocation().beginLine());
		}else {
			return null;
		}
	}
	
	private PGoTLAExpression readExpressionNoOperators(ListIterator<TLAToken> iter, int minColumn) {
		if(!lookaheadValidColumn(iter, minColumn)) {
			throw new RuntimeException("Expression interrupted by end of column");
		}
		PGoTLAExpression expr = null;
		expr = lookaheadNumber(iter, true);
		if(expr == null) {
			expr = lookaheadString(iter, true);
		}
		if(expr == null) {
			expr = lookaheadBoolean(iter, true);
		}
		if(expr != null) {
			return expr;
		}
		if(lookaheadBuiltinToken(iter, "(", true)) {
			expr = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, ")");
			return expr;
		}
		if(lookaheadBuiltinToken(iter, "<<", true)) {
			List<PGoTLAExpression> exprs = new ArrayList<>();
			do {
				exprs.add(readExpressionFromPrecedence(iter, 1, minColumn));
			}while(lookaheadBuiltinToken(iter, ",", true));
			// TODO: >>_
			expectBuiltinToken(iter, ">>");
			return new PGoTLATuple(-1, exprs);
		}
		// TODO: support GeneralIdentifier, as well as General* forms of the operators
		String id = lookaheadIdentifier(iter, true);
		if(id != null) {
			if(lookaheadValidColumn(iter, minColumn)) {
				if(lookaheadBuiltinToken(iter, "(", true)) {
					List<PGoTLAExpression> args = new ArrayList<>();
					do {
						args.add(readExpressionFromPrecedence(iter, 1, minColumn));
					}while(lookaheadValidColumn(iter, minColumn) && lookaheadBuiltinToken(iter, ",", true));
					expectBuiltinToken(iter, ")");
					return new PGoTLAOperatorCall(-1, id, args);
				}
			}
			return new PGoTLAVariable(id, -1);
		}
		if(lookaheadBuiltinToken(iter, "\\/", true)) {
			List<PGoTLAExpression> exprs = new ArrayList<>();
			do {
				TLAToken tok = iter.previous();
				iter.next();
				if(tok.column < minColumn) {
					iter.previous();
					break;
				}
				exprs.add(readExpressionFromPrecedence(iter, 1, tok.column));
			}while(lookaheadNewline(iter) && lookaheadBuiltinToken(iter, "\\/", true));
			
			PGoTLAExpression lhs = exprs.get(0);
			for(int i = 1; i < exprs.size(); ++i) {
				lhs = new PGoTLABinOp(-1, "/\\", lhs, exprs.get(0));
			}
			return lhs;
		}
		if(lookaheadBuiltinToken(iter, "/\\", true)) {
			List<PGoTLAExpression> exprs = new ArrayList<>();
			do {
				TLAToken tok = iter.previous();
				iter.next();
				if(tok.column < minColumn) {
					break;
				}
				exprs.add(readExpressionFromPrecedence(iter, 1, tok.column));
			}while(lookaheadNewline(iter) && lookaheadBuiltinToken(iter, "/\\", true));
			
			PGoTLAExpression lhs = exprs.get(0);
			for(int i = 1; i < exprs.size(); ++i) {
				lhs = new PGoTLABinOp(-1, "/\\", lhs, exprs.get(0));
			}
			return lhs;
		}
		if(lookaheadBuiltinToken(iter, "IF", true)) {
			PGoTLAExpression cond = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, "THEN");
			PGoTLAExpression tVal = readExpressionFromPrecedence(iter, 1, minColumn);
			expectBuiltinToken(iter, "ELSE");
			PGoTLAExpression fVal = readExpressionFromPrecedence(iter, 1, minColumn);
			return new PGoTLAIf(-1, cond, tVal, fVal);
		}
		throw new RuntimeException("TODO: expression, "+iter.next());
	}
	
	private boolean lookaheadValidColumn(ListIterator<TLAToken> iter, int minColumn) {
		skipNewlines(iter);
		if(!iter.hasNext()) return true;
		TLAToken tok = iter.next();
		iter.previous();
		return tok.column > minColumn;
	}
	
	private PGoTLAExpression readExpressionFromPrecedence(ListIterator<TLAToken> iter, int precedence, int minColumn) {
		if(precedence > 17) {
			return readExpressionNoOperators(iter, minColumn);
		}else {
			String op;
			PGoTLAExpression lhs = null;
			if(!lookaheadValidColumn(iter, minColumn)) {
				throw new RuntimeException("Expression interrupted by end of column");
			}
			if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, true)) != null) {
				if(PREFIX_OPERATORS_LOW_PRECEDENCE.get(op) <= precedence && PREFIX_OPERATORS_HI_PRECEDENCE.get(op) >= precedence) {
					lhs = new PGoTLAUnary(op, readExpressionFromPrecedence(iter, PREFIX_OPERATORS_HI_PRECEDENCE.get(op)+1, minColumn), -1);
				}else {
					iter.previous();
					lhs = readExpressionFromPrecedence(iter, precedence + 1, minColumn);
				}
			}else {
				lhs = readExpressionFromPrecedence(iter, precedence + 1, minColumn);
			}
			// end if we hit the end of a column
			if(!lookaheadValidColumn(iter, minColumn)) {
				return lhs;
			}

			if((op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, true)) != null) {
				if(INFIX_OPERATORS_LOW_PRECEDENCE.get(op) <= precedence && INFIX_OPERATORS_HI_PRECEDENCE.get(op) >= precedence ) {
					// TODO: error cases for when there are operator precedence conflicts
					// idea: pass HI precedence as starting precedence, making sure to accept repeats
					// of the same left-associative operator
					return new PGoTLABinOp(-1, op, lhs, readExpressionFromPrecedence(iter, 1, minColumn));
				}else {
					iter.previous();
				}
			}
			if((op = lookaheadBuiltinTokenOneOf(iter, POSTFIX_OPERATORS, true)) != null) {
				if(POSTFIX_OPERATORS_PRECEDENCE.get(op) == precedence) {
					return new PGoTLAUnary(op, lhs, -1);
				}else {
					iter.previous();
				}
			}
			return lhs;
		}
	}
	
	public PGoTLAExpression readExpression(ListIterator<TLAToken> iter) {
		PGoTLAExpression e = readExpressionFromPrecedence(iter, 1, -1);
		System.out.println("Read expression "+e);
		return e;
	}
	
	private PGoTLAModule readModule(ListIterator<TLAToken> iter) {
		expect4DashesOrMore(iter);
		expectBuiltinToken(iter, MODULE);
		String name = expectIdentifier(iter);
		expect4DashesOrMore(iter);
		List<String> exts = readExtends(iter);
		
		// accumulators for parts of the module
		List<String> variables = new ArrayList<String>();
		List<PGoTLAOpDecl> constants = new ArrayList<PGoTLAOpDecl>();
		Map<String, PGoTLAOperator> operators = new HashMap<String, PGoTLAOperator>();
		List<PGoTLAModule> submodules = new ArrayList<PGoTLAModule>();
		List<PGoTLAExpression> assumptions = new ArrayList<>();
		List<PGoTLAExpression> theorems = new ArrayList<>();
		
		while(!lookahead4EqualsOrMore(iter, true)) {
			skipAnnotations(iter);
			if(lookaheadBuiltinToken(iter, "VARIABLE", true) || lookaheadBuiltinToken(iter, "VARIABLES", true)) {
				variables.addAll(readVariables(iter));
			}else if(lookaheadBuiltinToken(iter, "CONSTANT", true) || lookaheadBuiltinToken(iter, "CONSTANTS", true)) {
				constants.addAll(readConstants(iter));
			}else if(lookaheadBuiltinTokenOneOf(iter, ASSUMPTION_TOKENS, true) != null) {
				// assumption
				assumptions.add(readExpression(iter));
			}else if(lookaheadBuiltinToken(iter, "THEOREM", true)) {
				// theorem
				theorems.add(readExpression(iter));
			}else if(lookahead4DashesOrMore(iter, true)) {
				iter.previous();
				submodules.add(readModule(iter));
			}else {
				// all things that can be local (shared optional LOCAL prefix)
				boolean isLocal = false;
				if(lookaheadBuiltinToken(iter, "LOCAL", true)) {
					isLocal = true;
				}
				String op;
				// instance is easy to spot
				if(lookaheadBuiltinToken(iter, "INSTANCE", true)) {
					// TODO: instance
					throw new RuntimeException("TODO: INSTANCE");
				// it's quite tricky to tell OperatorDefinition, FunctionDefinition and ModuleDefinition apart
				// so we parse them all together until we can tell what we're dealing with
				}else if((op = lookaheadBuiltinTokenOneOf(iter, PREFIX_OPERATORS, true)) != null) {
					// we know this is an operator definition
					String operand = expectIdentifier(iter);
					expectBuiltinToken(iter, "==");
					List<PGoTLAOpDecl> operands = new ArrayList<>();
					operands.add(new PGoTLAOpDeclIdentifier(operand));
					operators.put(op, new PGoTLAOperator(op, operands, readExpression(iter)));
				}else {
					String id = expectIdentifier(iter);
					if((op = lookaheadBuiltinTokenOneOf(iter, POSTFIX_OPERATORS, true)) != null) {
						System.out.println("Postfix def "+id+" "+op);
						// operator definition
						expectBuiltinToken(iter, "==");
						List<PGoTLAOpDecl> operands = new ArrayList<>();
						operands.add(new PGoTLAOpDeclIdentifier(id));
						operators.put(op,  new PGoTLAOperator(op, operands, readExpression(iter)));
					}else if((op = lookaheadBuiltinTokenOneOf(iter, INFIX_OPERATORS, true)) != null) {
						System.out.println("Infix def "+id+" "+op);
						// operator definition
						String rhs = expectIdentifier(iter);
						expectBuiltinToken(iter, "==");
						List<PGoTLAOpDecl> operands = new ArrayList<>();
						operands.add(new PGoTLAOpDeclIdentifier(id));
						operands.add(new PGoTLAOpDeclIdentifier(rhs));
						operators.put(op, new PGoTLAOperator(op, operands, readExpression(iter)));
					}else if(lookaheadBuiltinToken(iter, "[", true)) {
						// TODO: function definition
						throw new RuntimeException("TODO: function definition");
					}else{
						System.out.println("Must be classic opdecls, id "+id);
						List<PGoTLAOpDecl> opdecls = new ArrayList<PGoTLAOpDecl>();
						if(lookaheadBuiltinToken(iter, "(", true)) {
							do {
								opdecls.add(readOpDecl(iter));
							}while(lookaheadBuiltinToken(iter, COMMA, true));
							expectBuiltinToken(iter, ")");
						}
						expectBuiltinToken(iter, "==");
						if(lookaheadBuiltinToken(iter, "INSTANCE", true)) {
							// TODO: module definition
							throw new RuntimeException("TODO: module definition");
						}else {
							operators.put(id, new PGoTLAOperator(id, opdecls, readExpression(iter)));
						}
					}
				}
			}
		}
		return new PGoTLAModule(name, null, null);
	}
	
	public List<PGoTLAModule> readModules(){
		List<PGoTLAModule> modules = new ArrayList<PGoTLAModule>();
		
		ListIterator<TLAToken> iter = tokens.listIterator();
		while(iter.hasNext()) {
			modules.add(readModule(iter));
		}
		
		return modules;
	}
}
