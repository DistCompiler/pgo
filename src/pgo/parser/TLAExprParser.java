package pgo.parser;

import java.util.HashMap;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;

/**
 * TLAExpr Parser
 */
public class TLAExprParser {

	// the indexes that we parsed up to;
	private int cur;

	// the line number from the algorith .tla flie
	private int line;

	// the parsed result. Each element represents one complete clause
	private List<PGoTLAExpression> result;

	// which row of array to store result
	private int resultRow;

	// the tokens we are parsing
	private List<TLAToken> tokens;

	// the stack of operators we encountered
	private Stack<TLAToken> ops;

	// the stack of lhs of hte operators
	private Stack<PGoTLAExpression> exps;

	// the type of the "defaultInitValue" TLAToken.
	private static final int DEFAULT_VAL = 0;

	public TLAExprParser(TLAExpr tla, int line) throws PGoTransException {
		init(line);
		for (Vector<TLAToken> v : (Vector<Vector<TLAToken>>) tla.tokens) {
			tokens.addAll(v);
			tokens.add(null); // new line marker
		}

		parse();
	}

	public TLAExprParser(List<TLAToken> t, int line) throws PGoTransException {
		init(line);
		tokens = t;

		parse();
	}

	private void init(int line) throws PGoTransException {
		this.line = line;
		ops = new Stack<>();
		exps = new Stack<>();

		tokens = new Vector<>();
		cur = 0;
		resultRow = 0;
		result = new Vector<>();
	}

	private void parse() throws PGoTransException {
		while (hasNext()) {
			TLAToken tok = next();
			if (tok == null) {
				continue;
			}
			if (tok.type == TLAToken.BUILTIN) {
				if (tok.type == TLAToken.BUILTIN && tok.string.equals(",")) {
					// in the case of expressions like \E x \in S, y \in T... we
					// don't want the \E to get combined with just x \in S
					combineExps(opPrecedence.get(Dictionary.EXISTS) + 1);
					result.add(exps.pop());
					continue;
				}

				// this is built in tokens like "<<", "]" etc
				if (tok.string.equals("TRUE") || tok.string.equals("FALSE")) {
					parseBooleanToken(tok);
				} else {
					if (Dictionary.tokenDict.containsKey(tok.string)) {
						long mask = Dictionary.tokenDict.get(tok.string);
						if ((mask & Dictionary.VARIADIC_OP) > 0) {
							// in this case we take all exprs from the lhs and
							// all unparsed TLATokens from the rhs
							// We take the entire expression since any
							// surrounding context is already stripped (apart
							// from maybe the predicate operation on the ops
							// stack, if the op is such that)
							combineExps(opPrecedence.get(mask));
							Vector<PGoTLAExpression> left = new Vector<>(result);
							result.clear();
							left.addAll(exps);
							exps.clear();
							Vector<TLAToken> right = new Vector<>(tokens.subList(cur, tokens.size()));
							exps.push(new PGoTLAVariadic(tok.string, left, right, line));
							// we are done parsing; don't parse rhs twice
							cur = tokens.size();
						} else if ((mask & Dictionary.X_OP_X) > 0) {
							if (cur == 1 && (mask & (Dictionary.AND | Dictionary.OR)) > 0) {
								// this is the first item in a bulleted list of
								// and/or, so we can ignore it
								continue;
							}
							combineExps(opPrecedence.get(mask));
							ops.push(tok);
						} else if ((mask & Dictionary.OP_X) > 0) {
							ops.push(tok);
						} else if ((mask & Dictionary.CONTAINER_TOK) > 0) {
							parseContainerToken(tok);
						}
					} else {
						throw new PGoTransException("Unknown identifier token: \"" + tok.string + "\"", line);
					}
				}
			} else if (tok.type == TLAToken.IDENT) {
				// this is identifier to a variable or function call
				parseIdentifierToken(tok);
			} else if (tok.type == TLAToken.NUMBER) {
				// this is just a number
				parseNumberToken(tok);
			} else if (tok.type == TLAToken.STRING) {
				// this is just a string
				parseStringToken(tok);
			} else if (tok.type == DEFAULT_VAL) {
				// this means the TLA expr is blank
				result.add(new PGoTLAExpression.PGoTLADefault(line));
				break;
			} else {
				throw new PGoTransException("Unknown token: \"" + tok.string + "\"", line);
			}
		}
		combineExps(0);
		assert (exps.size() <= 1);
		if (!exps.isEmpty()) {
			result.add(exps.pop());
		}
	}

	// Returns null if new line
	private TLAToken next() {
		assert (hasNext());
		TLAToken ret = tokens.get(cur++);
		if (ret == null) {
			line++;
		}
		return ret;
	}

	private boolean hasNext() {
		return cur < tokens.size();
	}

	// peaks at next token
	private boolean lookAheadMatch(int tokenType, String token) {
		if (cur < tokens.size() && tokens.get(cur) != null) {
			return (tokens.get(cur).type == tokenType) && tokens.get(cur).string.equals(token);
		} else if (cur + 1 < tokens.size()) {
			return (tokens.get(cur + 1).type == tokenType) && tokens.get(cur + 1).string.equals(token);
		}
		return false;
	}

	/**
	 * Combine the expressions on the stack with the operators on the stack, as
	 * long as their precedence is at least equal to the current operator.
	 * 
	 * @param precedence
	 *            the precedence of the current operator, as specified by the
	 *            opPrecedence dict. Use 0 to combine w/ all operations
	 */
	private void combineExps(int precedence) {
		while (!ops.isEmpty() && opPrecedence.get(Dictionary.tokenDict.get(ops.peek().string)) >= precedence) {
			TLAToken prevT = ops.pop();
			if ((Dictionary.tokenDict.get(prevT.string) & Dictionary.X_OP_X) > 0) {
				PGoTLAExpression rexps = exps.pop();
				PGoTLAExpression lexps = exps.pop();
				parseXOpXToken(prevT, lexps, rexps);
			} else {
				assert ((Dictionary.tokenDict.get(prevT.string) & Dictionary.OP_X) > 0);
				PGoTLAExpression rexps = exps.pop();
				parseOpXToken(prevT, rexps);
			}
		}
	}

	/**
	 * The following methods parses a single token, and advances forward as
	 * appropriate
	 */
	private void parseStringToken(TLAToken tlaToken) {
		exps.push(new PGoTLAString(tlaToken.string, line));
	}

	private void parseNumberToken(TLAToken tlaToken) {
		exps.push(new PGoTLANumber(tlaToken.string, line));
	}

	private void parseIdentifierToken(TLAToken tlaToken) throws PGoTransException {
		if (lookAheadMatch(TLAToken.BUILTIN, "(")) {
			// don't include outer brackets
			cur++;
			Vector<TLAToken> contained = advanceUntilMatching(")", "(", TLAToken.BUILTIN);
			exps.push(new PGoTLAFunctionCall(tlaToken.string, contained, line));
		} else if (lookAheadMatch(TLAToken.BUILTIN, "[")) {
			// map access
			cur++;
			Vector<TLAToken> contained = advanceUntilMatching("]", "[", TLAToken.BUILTIN);
			exps.push(new PGoTLAFunctionCall(tlaToken.string, contained, line));
		} else {
			exps.push(new PGoTLAVariable(tlaToken.string, line));
		}
	}

	private void parseBooleanToken(TLAToken tlaToken) {
		exps.push(new PGoTLABool(tlaToken.string, line));
	}

	// Parse a container token eg ( ) [ ] { } << >>
	private void parseContainerToken(TLAToken tok) throws PGoTransException {
		assert (Dictionary.tokenDict.containsKey(tok.string));
		long mask = Dictionary.tokenDict.get(tok.string);
		int oldLine = line;
		if (mask == Dictionary.OPEN_PAREN) {
			Vector<TLAToken> between = advanceUntilMatching(")", "(", TLAToken.BUILTIN);
			TLAExprParser parser = new TLAExprParser(between, oldLine);
			exps.push(new PGoTLAGroup(parser.getResult(), oldLine));
		} else if (mask == Dictionary.SQR_PAREN_O) {
			Vector<TLAToken> between = advanceUntilMatching("]", "[", TLAToken.BUILTIN);
			exps.push(new PGoTLAArray(between, oldLine));
		} else if (mask == Dictionary.CURLY_OPEN) {
			Vector<TLAToken> between = advanceUntilMatching("}", "{", TLAToken.BUILTIN);
			exps.push(new PGoTLASet(between, oldLine));
		} else if (mask == Dictionary.ARROW_OPEN) {
			Vector<TLAToken> between = advanceUntilMatching(">>", "<<", TLAToken.BUILTIN);

			// << >> are tuples in PlusCal. Most of the time they converted to
			// channels since they are used for communication. But more safety
			// they should be either a slice for tuple, or channel for
			// communication. We distinguish between these later when converting
			// to Go.
			exps.push(new PGoTLAArray(between, line));
		}
	}

	// Parse an operator with 2 arguments on either side
	private void parseXOpXToken(TLAToken prevT, PGoTLAExpression lexps, PGoTLAExpression rexps) {
		assert (Dictionary.tokenDict.containsKey(prevT.string));
		long mask = Dictionary.tokenDict.get(prevT.string);
		if (mask == Dictionary.SIMPLE_ARITHMETIC || mask == Dictionary.EXPONENT) {
			exps.push(new PGoTLASimpleArithmetic(prevT.string, lexps, rexps, line));
		} else if ((mask & Dictionary.BOOL_OP) != 0) {
			exps.push(new PGoTLABoolOp(prevT.string, lexps, rexps, line));
		} else if (mask == Dictionary.SEQUENCE) {
			exps.push(new PGoTLASequence(lexps, rexps, line));
		} else if ((mask & Dictionary.SET_OP) != 0) {
			exps.push(new PGoTLASetOp(prevT.string, lexps, rexps, line));
		} else if (mask == Dictionary.STRING_APPEND) {
			// TODO handle (issue #6)
		} else {
			assert false;
		}
	}

	// Parse an operator with only right side argument
	private void parseOpXToken(TLAToken prevT, PGoTLAExpression rexps) {
		exps.push(new PGoTLAUnary(prevT.string, rexps, line));
	}

	/**
	 * Advance until the next closing endToken. Every occurrence of beginToken
	 * will require an extra closing token, which is the begin token in param.
	 * We expect the current token to be after the begin that we are trying to
	 * enclose.
	 * 
	 * Returns all the token in between
	 * 
	 * @param tokenType
	 */
	private Vector<TLAToken> advanceUntilMatching(String endToken, String begin, int tokenType) {
		int numExtra = 0;

		Vector<TLAToken> ret = new Vector<TLAToken>();

		while (hasNext()) {

			TLAToken tok = next();
			if (tok == null) {
				line++;
			} else if (tok.string.equals(endToken) && tok.type == tokenType) {
				numExtra--;
				if (numExtra < 0) {
					return ret;
				}
			} else if (tok.string.equals(begin) && tok.type == tokenType) {
				numExtra++;
			}

			ret.add(tok);
		}
		return ret;
	}

	public static class Dictionary {
		/*
		 * bitmasks of various tla tokens. We use bitmask as a token could be
		 * multiple possibilities until we check the corresponding variable
		 * types. Not listed in a particular order; operator precedence is
		 * handled by the opPrecedence dict.
		 */

		// arithmetic operations
		public static final long EXPONENT = 1 << 0;
		// don't care for arithmetic operation orders. Go will take care of it.
		public static final long SIMPLE_ARITHMETIC = EXPONENT << 1;

		// string operations
		public static final long STRING_APPEND = SIMPLE_ARITHMETIC << 1;

		// boolean operations
		public static final long AND = STRING_APPEND << 1;
		public static final long OR = AND << 1;
		public static final long NEGATE = OR << 1;
		public static final long SMALLER = NEGATE << 1;
		public static final long GREATER = SMALLER << 1;
		public static final long SMALLER_EQ = GREATER << 1;
		public static final long GREATER_EQ = SMALLER_EQ << 1;
		public static final long NOT_EQ = GREATER_EQ << 1;
		public static final long EQUAL = NOT_EQ << 1; // 11 bits
		public static final long COMPARATOR = NOT_EQ | SMALLER | GREATER | SMALLER_EQ | GREATER_EQ | EQUAL;
		public static final long BOOL_OP = AND | OR | NEGATE | COMPARATOR;

		// set operations
		public static final long SUCH_THAT = EQUAL << 1;
		public static final long SEQUENCE = SUCH_THAT << 1;
		public static final long UNION = SEQUENCE << 1;
		public static final long ELEMENT_UNION = UNION << 1;
		public static final long POWER_SET = ELEMENT_UNION << 1;
		public static final long INTERSECTION = POWER_SET << 1;
		public static final long SET_DIFFERENCE = INTERSECTION << 1;
		public static final long IS_IN = SET_DIFFERENCE << 1;
		public static final long NOT_IN = IS_IN << 1;
		public static final long SUBSET = NOT_IN << 1;
		public static final long CARTESIAN_PRODUCT = SUBSET << 1;
		public static final long SET_OP = SEQUENCE | UNION | ELEMENT_UNION | POWER_SET | INTERSECTION | SET_DIFFERENCE
				| IS_IN | NOT_IN | SUBSET | CARTESIAN_PRODUCT;

		// used in array declarations
		public static final long MAPS_TO = CARTESIAN_PRODUCT << 1;
		public static final long EXCEPT = MAPS_TO << 1;
		public static final long DOMAIN = EXCEPT << 1;
		public static final long TO = DOMAIN << 1;
		public static final long ARRAY_OP = MAPS_TO | EXCEPT | DOMAIN | TO;

		public static final long IGNORE = TO << 1;

		// predicate operations
		public static final long CHOOSE = IGNORE << 1;
		public static final long FOR_ALL = CHOOSE << 1;
		public static final long EXISTS = FOR_ALL << 1;

		// container tokens. we only need to know when we hit the start.
		// ( ) parens
		public static final long OPEN_PAREN = EXISTS << 1;
		// [ ] parens
		public static final long SQR_PAREN_O = OPEN_PAREN << 1;
		// { } parens
		public static final long CURLY_OPEN = SQR_PAREN_O << 1;
		// << >> parens
		public static final long ARROW_OPEN = CURLY_OPEN << 1; // 31

		public static final long CONTAINER_TOK = OPEN_PAREN | SQR_PAREN_O | CURLY_OPEN | ARROW_OPEN;

		// operators with 2 arguments on either side
		public static final long X_OP_X = (SIMPLE_ARITHMETIC | BOOL_OP | EXPONENT | STRING_APPEND | SET_OP | TO)
				& ~(NEGATE | ELEMENT_UNION | POWER_SET | DOMAIN);
		// right side argument operators
		public static final long OP_X = NEGATE | ELEMENT_UNION | POWER_SET | CHOOSE | FOR_ALL | EXISTS | DOMAIN;
		// operators with one argument on one side and a variable number on the
		// other
		public static final long VARIADIC_OP = SUCH_THAT | MAPS_TO | EXCEPT;

		private static final HashMap<String, Long> tokenDict = new HashMap<String, Long>() {
			{
				put("+", SIMPLE_ARITHMETIC);
				put("-", SIMPLE_ARITHMETIC);
				put("*", SIMPLE_ARITHMETIC);
				put("/", SIMPLE_ARITHMETIC);
				put("\\div", SIMPLE_ARITHMETIC);
				put("%", SIMPLE_ARITHMETIC);
				put("^", EXPONENT);

				put("\\o", STRING_APPEND);

				put("/\\", AND);
				put("\\land", AND);
				put("\\lor", OR);
				put("\\/", OR);
				put("~", NEGATE);
				put("\\lnot", NEGATE);
				put("\\neg", NEGATE);
				put("#", NOT_EQ);
				put("/=", NOT_EQ);
				put("<", SMALLER);
				put(">", GREATER);
				put("<=", SMALLER_EQ);
				put("=<", SMALLER_EQ);
				put("\\leq", SMALLER_EQ);
				put(">=", GREATER_EQ);
				put("\\geq", GREATER_EQ);
				put("==", EQUAL);
				put("=", EQUAL);

				put("\\in", IS_IN);
				put("\\notin", NOT_IN);
				put("\\cup", UNION);
				put("\\union", UNION);
				put("UNION", ELEMENT_UNION);
				put("\\subseteq", SUBSET);
				put("\\cap", INTERSECTION);
				put("\\intersect", INTERSECTION);
				put("SUBSET", POWER_SET);
				put("\\", SET_DIFFERENCE);
				put(":", SUCH_THAT);
				put("..", SEQUENCE);
				put("\\X", CARTESIAN_PRODUCT);
				put("\\times", CARTESIAN_PRODUCT);

				put("|->", MAPS_TO);
				put("EXCEPT", EXCEPT);
				put("DOMAIN", DOMAIN);
				put("->", TO);
				put("!", IGNORE);

				put("CHOOSE", CHOOSE);
				put("\\A", FOR_ALL);
				put("\\E", EXISTS);

				put("<<", ARROW_OPEN);
				put("{", CURLY_OPEN);
				put("[", SQR_PAREN_O);
				put("(", OPEN_PAREN);
				// TODO (issue #11) check
				// http://lamport.azurewebsites.net/tla/p-manual.pdf
				// and
				// https://pdfs.semanticscholar.org/6ed6/404cc710511c2a77d190ff10f83e46324d91.pdf
				// for more tla expressions and support necessary ones.
				// pcal.PcalBuiltInSymbols has a whole list of stuff too
			}
		};

	}

	/*
	 * Maps a Dictionary bitmask to the corresponding operator precedence.
	 * Higher precedence => higher number. Operator precedence table found at
	 * http://lamport.azurewebsites.net/tla/summary-standalone.pdf
	 */
	private static final HashMap<Long, Integer> opPrecedence = new HashMap<Long, Integer>() {
		{
			put(Dictionary.CHOOSE, 1);
			put(Dictionary.FOR_ALL, 1);
			put(Dictionary.EXISTS, 1);
			put(Dictionary.SUCH_THAT, 2);
			put(Dictionary.EXCEPT, 2);
			put(Dictionary.MAPS_TO, 2);
			put(Dictionary.TO, 2);
			put(Dictionary.AND, 3);
			put(Dictionary.OR, 3);
			put(Dictionary.NEGATE, 4);
			put(Dictionary.NOT_EQ, 5);
			put(Dictionary.SMALLER, 5);
			put(Dictionary.SMALLER_EQ, 5);
			put(Dictionary.EQUAL, 5);
			put(Dictionary.GREATER, 5);
			put(Dictionary.GREATER_EQ, 5);
			put(Dictionary.IS_IN, 5);
			put(Dictionary.NOT_IN, 5);
			put(Dictionary.SUBSET, 5);
			put(Dictionary.SET_DIFFERENCE, 8);
			put(Dictionary.INTERSECTION, 8);
			put(Dictionary.UNION, 8);
			put(Dictionary.ELEMENT_UNION, 8);
			put(Dictionary.POWER_SET, 8);
			put(Dictionary.CARTESIAN_PRODUCT, 9);
			put(Dictionary.SEQUENCE, 9);
			put(Dictionary.DOMAIN, 9);
			put(Dictionary.SIMPLE_ARITHMETIC, 13);
			put(Dictionary.STRING_APPEND, 13);
			put(Dictionary.EXPONENT, 14);
			put(Dictionary.OPEN_PAREN, 18);
			put(Dictionary.SQR_PAREN_O, 18);
			put(Dictionary.ARROW_OPEN, 18);
			put(Dictionary.CURLY_OPEN, 18);
		}
	};

	public List<PGoTLAExpression> getResult() {
		return result;
	}
}
