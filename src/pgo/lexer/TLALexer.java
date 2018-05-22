package pgo.lexer;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import pgo.util.SourceLocation;

/**
 * A simple TLA+ lexer that tries to replicate the TLC's lexing behaviour.
 * 
 * For simple changes like adding a builtin token type you can just add
 * it to the BUILTIN list. For more complex changes editing the readTokens
 * method may be necessary.
 * 
 * Notable feature: extracts PGo annotations as their own tokens so they can
 * be easily parsed later.
 */
public class TLALexer {
	
	static final Pattern WHITESPACE = Pattern.compile("\\s+");
	
	static final Pattern MODULE_START = Pattern.compile("----+");
	static final Pattern MODULE_END = Pattern.compile("====+");
	
	static final String[] BUILTIN = {
		// boolean constants
		"TRUE",
		"FALSE",
		
		"ASSUME",
		"ELSE",
		"LOCAL",
		"UNION",
		"ASSUMPTION",
		"ENABLED",
		"MODULE",
		"VARIABLE",
		"AXIOM",
		"EXCEPT",
		"OTHER",
		"VARIABLES",
		"CASE",
		"EXTENDS",
		"SF_",
		"WF_",
		"CHOOSE",
		"IF",
		"SUBSET",
		"WITH",
		"CONSTANT",
		"IN",
		"THEN",
		"CONSTANTS",
		"INSTANCE",
		"THEOREM",
		"DOMAIN",
		"LET",
		"UNCHANGED",
		// comma
		",",
		// parens
		"(",
		")",
		// brackets
		"[",
		"]",
		"]_",
		// braces
		"{",
		"}",
		// : for use in \E
		":",
		// instance prefix part i.e "a!b(...)"
		"!",
		// quantifiers
		"\\A",
		"\\E",
		"\\AA",
		"\\EE",
		// tuple delimiters
		"<<",
		">>",
		">>_",
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
		"<=",
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
		// prefix ops (alpha)
		"\\lnot",
		"\\neg",
		"[]",
		"<>",
		"DOMAIN",
		"ENABLED",
		"SUBSET",
		"UNCHANGED",
		"UNION",
		// prefix ops (non-alpha)
		"-",
		"~",
		"[]",
		"<>",
		// postfix ops
		"^+",
		"^*",
		"^#",
		"'",
		// operator definition
		"==",
		// functions and records
		"->",
		"|->",
	};
	
	static final Pattern IDENT = Pattern.compile("[a-z0-9_A-Z]*[a-zA-Z][a-z0-9_A-Z]*");
	
	static final Pattern[] NUMBER = {
		Pattern.compile("[0-9]*\\.[0-9]+"),
		Pattern.compile("[0-9]+"),
		Pattern.compile("\\[bB][01]+"),
		Pattern.compile("\\[oO][0-7]+"),
		Pattern.compile("\\[hH][0-9a-fA-F]+"),
	};
	
	static final Pattern STRING = Pattern.compile("\"([^\"]*)\"");
	
	static final Pattern COMMENT_START = Pattern.compile("\\(\\*");
	static final Pattern COMMENT_END = Pattern.compile("\\*\\)");
	static final Pattern LINE_COMMENT = Pattern.compile("\\\\\\*");
	
	static final Pattern PGO_ANNOTATION = Pattern.compile("@PGo\\{(.*)\\}@PGo");
	
	static final Pattern BEGIN_TRANSLATION = Pattern.compile("\\\\\\*+ BEGIN TRANSLATION$");
	static final Pattern END_TRANSLATION = Pattern.compile("\\\\\\*+ END TRANSLATION$");
	
	List<String> lines;
	Path filename;

	boolean moduleRequired;
	
	public TLALexer(Path filename) throws IOException {
		lines = Files.readAllLines(filename);
		this.moduleRequired = true;
		this.filename = filename;
	}
	
	public TLALexer(Path filename, List<String> lines) {
		this.lines = lines;
		this.moduleRequired = true;
		this.filename = filename;
	}
	
	/**
	 * @param yes whether to require that the input begins with a TLA module declaration, defaults to true
	 */
	public void requireModule(boolean yes) {
		this.moduleRequired = yes;
	}
	
	private TLAToken makeToken(String value, TLATokenType type, int column, int line) {
		return new TLAToken(value, type, new SourceLocation(filename, line, line, column, column + value.length()));
	}
	
	/**
	 * @return a list of tokens scanned from the lines the lexer was given
	 * @throws PGoTLALexerException if the lexer cannot understand part of the input
	 */
	public List<TLAToken> readTokens() throws PGoTLALexerException{
		List<TLAToken> tokens = new ArrayList<TLAToken>();
		// nested module count*2; is 0 if we are not in a module
		// 2 for in one module, 4 for in a nested module, etc...
		// note: moduleRequired is used to get the lexer to read subsets of files,
		// like expressions
		int moduleStack = moduleRequired? 0 : 2;
		// nested comment count, 0 for no comment, 1 for comment, 2
		// for comment in a comment, etc...
		int commentStack = 0;
		int lineNum = 0;
		for(String line : lines) {
			++lineNum;
			int column = 0;
			boolean inLineComment = false;
			int oldColumn = -1;
			while(column < line.length()) {
				// test for the lexer getting stuck, either the lexer has a problem
				// or the source file does
				if(column == oldColumn) {
					throw new PGoTLALexerException(lineNum, "got stuck at column "+(column+1), tokens);
				}
				oldColumn = column;
				
				if(moduleStack == 0) {
					Matcher m = MODULE_START.matcher(line);
					if(m.find()) {
						column = m.end();
						++moduleStack;
						tokens.add(makeToken(m.group(), TLATokenType.BUILTIN, m.start()+1, lineNum));
					}else {
						column = line.length();
					}
				}else if(commentStack > 0) {
					Matcher m = PGO_ANNOTATION.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						//tokens.add(makeToken(m.group(1), m.start(1)+1, PGoTLATokenCategory.PGO_ANNOTATION, lineNum));
						column = m.end();
						continue;
					}
					
					// this is currently redundant, but ensures that commentStack
					// holds the correct value till the end of the line
					m = LINE_COMMENT.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						++commentStack;
						inLineComment = true;
						column = m.end();
						continue;
					}
					
					m = COMMENT_END.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						--commentStack;
						column = m.end();
						continue;
					}
					
					m = COMMENT_START.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						++commentStack;
						column = m.end();
						continue;
					}
					
					// if no comment operators are found, move to the next character and try again
					// this is inefficient, but alternatives make the code complicated
					++column;
				}else {
					Matcher m = WHITESPACE.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						continue;
					}
					
					m = BEGIN_TRANSLATION.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						tokens.add(makeToken(m.group(), TLATokenType.BEGIN_TRANSLATION, m.start()+1, lineNum));
						++commentStack;
						inLineComment = true;
						continue;
					}
					
					m = END_TRANSLATION.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						tokens.add(makeToken(m.group(), TLATokenType.END_TRANSLATION, m.start()+1, lineNum));
						++commentStack;
						inLineComment = true;
						continue;
					}
					
					// handle reaching the beginning of a comment (both line and delimited)
					m = COMMENT_START.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						++commentStack;
						continue;
					}
					
					m = LINE_COMMENT.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						++commentStack;
						inLineComment = true;
						continue;
					}
					
					// check for the "-----..." that is part of MODULE ...
					m = MODULE_START.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						++moduleStack;
						tokens.add(makeToken(m.group(), TLATokenType.BUILTIN, m.start()+1, lineNum));
						continue;
					}
					
					// check for the end of the module
					m = MODULE_END.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						column = m.end();
						moduleStack -= 2;
						tokens.add(makeToken(m.group(), TLATokenType.BUILTIN, m.start()+1, lineNum));
						continue;
					}
					
					// try to match an identifier
					String possibleIdentifier = null;
					int possibleIdentifierEnd = 0;
					m = IDENT.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						possibleIdentifier = m.group();
						possibleIdentifierEnd = m.end();
					}
					
					// try to match the biggest number we can
					String possibleNumber = null;
					int possibleNumberEnd = 0;
					for(Pattern numberPattern : NUMBER) {
						m = numberPattern.matcher(line);
						m.region(column, line.length());
						if(m.lookingAt()) {
							String group = m.group();
							if(possibleNumber != null) {
								if(group.length() > possibleNumber.length()) {
									possibleNumber = group;
									possibleNumberEnd = m.end();
								}
							}else {
								possibleNumber = group;
								possibleNumberEnd = m.end();
							}
						}
					}
					
					// match the longest alphanumeric builtin we can
					String possibleBuiltin = null;
					int possibleBuiltinEnd = 0;
					for(String builtin : BUILTIN) {
						if(possibleBuiltin != null && builtin.length() < possibleBuiltin.length()) {
							continue;
						}
						if(line.regionMatches(column, builtin, 0, builtin.length())){
							possibleBuiltin = builtin;
							possibleBuiltinEnd = column + builtin.length();
						}
					}
					
					// now reconcile the tokens we generated:
					// if a possible identifier is longer than a builtin, it's an identifier. Otherwise it's the
					// builtin
					if(possibleIdentifier != null && possibleBuiltin != null) {
						if(possibleIdentifier.length() > possibleBuiltin.length()) {
							tokens.add(makeToken(possibleIdentifier, TLATokenType.IDENT, column+1, lineNum));
							column = possibleIdentifierEnd;
						}else {
							tokens.add(makeToken(possibleBuiltin, TLATokenType.BUILTIN, column+1, lineNum));
							column = possibleBuiltinEnd;
						}
						continue;
					}
					// if it didn't match any builtins but could have been an identifier, it was an identifier
					if(possibleIdentifier != null) {
						tokens.add(makeToken(possibleIdentifier, TLATokenType.IDENT, column+1, lineNum));
						column = possibleIdentifierEnd;
					}
					// numbers trump things like the dot operator
					if(possibleNumber != null) {
						tokens.add(makeToken(possibleNumber, TLATokenType.NUMBER, column+1, lineNum));
						column = possibleNumberEnd;
						continue;
					}
					// builtins not matching any identifiers or numbers are treated as builtins
					if(possibleBuiltin != null) {
						tokens.add(makeToken(possibleBuiltin, TLATokenType.BUILTIN, column+1, lineNum));
						column = possibleBuiltinEnd;
						continue;
					}
					
					// test for strings
					m = STRING.matcher(line);
					m.region(column, line.length());
					if(m.lookingAt()) {
						tokens.add(makeToken(m.group(1), TLATokenType.STRING, m.start()+1, lineNum));
						column = m.end();
						continue;
					}
				}
			}
			// if we were in a line comment, we aren't anymore
			// since we reached the end of the line
			if(inLineComment) {
				--commentStack;
			}
		}
		return tokens;
	}
}
