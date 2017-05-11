package pgo.parser;

import java.util.HashMap;
import java.util.Stack;
import java.util.Vector;

import pcal.TLAExpr;
import pcal.TLAToken;
import pgo.model.tla.*;
import pgo.trans.PGoTransException;

/**
 * TLAExpr Parser
 * 
 *
 */
public class TLAExprParser {

	// the indexes that we parsed up to;
	private int cur;

	// the line number from the algorith .tla flie
	private int line;

	// the parsed result. Each element represents one complete clause
	private Vector<PGoTLA> result;

	// which row of array to store result
	private int resultRow;

	// the tokens we are parsing
	private Vector<TLAToken> tokens;

	// the stack of operators we encountered
	private Stack<TLAToken> ops;

	// the stack of lhs of hte operators
	private Stack<PGoTLA> exps;

	public TLAExprParser(TLAExpr tla, int line) throws PGoTransException {
		init(line);
		for (Vector<TLAToken> v : (Vector<Vector<TLAToken>>) tla.tokens) {
			tokens.addAll(v);
			tokens.add(null); // new line marker
		}

		parse();
	}

	public TLAExprParser(Vector<TLAToken> t, int line) throws PGoTransException {
		init(line);
		tokens = t;

		parse();
	}

	private void init(int line) throws PGoTransException {
		this.line = line;
		ops = new Stack<TLAToken>();
		exps = new Stack<PGoTLA>();

		tokens = new Vector<TLAToken>();
		cur = 0;
		resultRow = 0;
		result = new Vector<PGoTLA>();
	}

	private void parse() throws PGoTransException {
		while (hasNext()) {
			TLAToken tok = next();
			if (tok == null) {
				continue;
			}
			if (tok.type == TLAToken.BUILTIN) {
				if (tok.type == TLAToken.BUILTIN && tok.string.equals(",")) {
					if (!ops.isEmpty()) {
						TLAToken prevT = ops.pop();
						PGoTLA rexps = exps.pop();
						PGoTLA lexps = exps.pop();
						parseXOpXToken(prevT, lexps, rexps);
					}
					result.add(exps.pop());
					continue;
				}

				// this is built in tokens like "<<", "]" etc
				if (tok.string.equals("TRUE") || tok.string.equals("FALSE")) {
					parseBooleanToken(tok);
				} else {
					if (Dictionary.tokenDict.containsKey(tok.string)) {
						int mask = Dictionary.tokenDict.get(tok.string);
						if ((mask & Dictionary.X_OP_X) > 0) {
							while (!ops.isEmpty()
									&& opPrecedence.get(Dictionary.tokenDict.get(ops.peek().string)) >= opPrecedence.get(mask)) {
								TLAToken prevT = ops.pop();
								PGoTLA rexps = exps.pop();
								PGoTLA lexps = exps.pop();
								parseXOpXToken(prevT, lexps, rexps);
							}
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
			} else {
				throw new PGoTransException("Unknown token: \"" + tok.string + "\"", line);
			}
		}
		while (!ops.isEmpty()) {
			TLAToken prevT = ops.pop();
			PGoTLA rexps = exps.pop();
			PGoTLA lexps = exps.pop();
			parseXOpXToken(prevT, lexps, rexps);
		}
		assert (exps.size() == 1);
		result.add(exps.pop());
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

	/**
	 * Handle single token expression, adding it to the stack or combining with the previous operator as appropriate
	 */
	private void handleSimpleExp(PGoTLA tok) {
		if (ops.isEmpty()) {
			exps.push(tok);
		} else {
			if ((Dictionary.tokenDict.get(ops.peek().string) & Dictionary.OP_X) > 0) {
				parseOpXToken(ops.pop(), tok);
			} else {
				exps.push(tok);
			}
		}
	}

	// peaks at next token
	private boolean lookAheadMatch(int tokenType, String token) {
		if (cur + 1 < tokens.size()) {
			return ((tokens.get(cur + 1).type == tokenType) && tokens.get(cur + 1).string.equals(token));
		}
		return false;
	}

	/**
	 * The following methods parses a single token, and advances forward as appropriate
	 */
	private void parseStringToken(TLAToken tlaToken) {
		handleSimpleExp(new PGoTLAString(tlaToken.string, line));
	}

	private void parseNumberToken(TLAToken tlaToken) {
		handleSimpleExp(new PGoTLANumber(tlaToken.string, line));
	}

	private void parseIdentifierToken(TLAToken tlaToken) throws PGoTransException {
		if (lookAheadMatch(TLAToken.BUILTIN, "(")) {
			Vector<TLAToken> contained = advanceUntilMatching(")", "(", TLAToken.BUILTIN);
			handleSimpleExp(new PGoTLAFunction(tlaToken.string, contained, line));
		} else {
			handleSimpleExp(new PGoTLAVariable(tlaToken.string, line));
		}
	}

	private void parseBooleanToken(TLAToken tlaToken) {
		handleSimpleExp(new PGoTLABool(tlaToken.string, line));
	}

	// Parse a container token eg ( ) [ ] { } << >>
	private void parseContainerToken(TLAToken tok) throws PGoTransException {
		assert (Dictionary.tokenDict.containsKey(tok.string));
		int mask = Dictionary.tokenDict.get(tok.string);
		int oldLine = line;
		if (mask == Dictionary.OPEN_PAREN) {
			Vector<TLAToken> between = advanceUntilMatching(")", "(", TLAToken.BUILTIN);
			TLAExprParser parser = new TLAExprParser(between, oldLine);
			handleSimpleExp(new PGoTLAGroup(parser.getResult(), oldLine));
		} else if (mask == Dictionary.SQR_PAREN_O) {
			Vector<TLAToken> between = advanceUntilMatching("]", "[", TLAToken.BUILTIN);
			handleSimpleExp(new PGoTLAArray(between, oldLine));
		} else if (mask == Dictionary.CURLY_OPEN) {
			Vector<TLAToken> between = advanceUntilMatching("}", "{", TLAToken.BUILTIN);
			handleSimpleExp(new PGoTLASet(between, oldLine));
		} else if (mask == Dictionary.ARROW_OPEN) {
			Vector<TLAToken> between = advanceUntilMatching(">>", "<<", TLAToken.BUILTIN);

			// << >> are tuples in PlusCal. Most of the time they converted to
			// channels since they are used for communication. But more safety
			// they should be either a slice for tuple, or channel for
			// communication.
			//
			// TODO distinguish this. I think we have to do this later on in the
			// code when converting to go, then we can check the types of the
			// variables from annotation to determine slice vs chan.
			handleSimpleExp(new PGoTLAArray(between, line)); // TODO
			// support
		}
	}

	// Parse an operator with 2 arguments on either side
	private void parseXOpXToken(TLAToken prevT, PGoTLA lexps, PGoTLA rexps) {
		assert (Dictionary.tokenDict.containsKey(prevT.string));
		int mask = Dictionary.tokenDict.get(prevT.string);
		if (mask == Dictionary.SIMPLE_ARITHMETIC || mask == Dictionary.EXPONENT) {
			handleSimpleExp(new PGoTLASimpleArithmetic(prevT.string, lexps, rexps, line));
		} else if ((mask & Dictionary.BOOL_OP) != 0) {
			handleSimpleExp(new PGoTLABoolOp(prevT.string, lexps, rexps, line));
		} else if (mask == Dictionary.SEQUENCE) {
			handleSimpleExp(new PGoTLASequence(lexps, rexps, line));
		} else if ((mask & Dictionary.SET_OP) != 0) {
			handleSimpleExp(new PGoTLASetOp(prevT.string, lexps, rexps, line));
		} else {
			assert false;
		}
		// TODO add more operators that we have
	}

	// Parse an operator with only right side argument
	private void parseOpXToken(TLAToken prevT, PGoTLA rexps) {
		// TODO Auto-generated method stub

	}

	/**
	 * Advance until the next closing endToken. Every occurrence of beginToken will require an extra closing token, which is the
	 * begin token in param. We expect the current token to be after the begin that we are trying to enclose.
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
		 * bitmasks of various tla tokens. We use bitmask as a token could be multiple possibilities until we check the
		 * corresponding variable types. Not listed in a particular order; operator precedence is handled by the opPrecedence
		 * dict.
		 */

		// arithmetic operations
		public static final int EXPONENT = 1 << 0;
		// don't care for arithmetic operation orders. Go will take care of it.
		public static final int SIMPLE_ARITHMETIC = EXPONENT << 1;

		// string operations
		public static final int STRING_APPEND = SIMPLE_ARITHMETIC << 1;

		// boolean operations
		public static final int AND = STRING_APPEND << 1;
		public static final int OR = AND << 1;
		public static final int NEGATE = OR << 1;
		public static final int SMALLER = NEGATE << 1;
		public static final int GREATER = SMALLER << 1;
		public static final int SMALLER_EQ = GREATER << 1;
		public static final int GREATER_EQ = SMALLER_EQ << 1;
		public static final int NOT_EQ = GREATER_EQ << 1;
		public static final int EQUAL = NOT_EQ << 1; // 11 bits
		public static final int COMPARATOR = NOT_EQ | SMALLER | GREATER | SMALLER_EQ | GREATER_EQ | EQUAL;
		public static final int BOOL_OP = AND | OR | NEGATE | COMPARATOR;

		// set operations
		public static final int SUCH_THAT = EQUAL << 1;
		public static final int SEQUENCE = SUCH_THAT << 1;
		public static final int UNION = SEQUENCE << 1;
		public static final int ELEMENT_UNION = UNION << 1;
		public static final int POWER_SET = ELEMENT_UNION << 1;
		public static final int INTERSECTION = POWER_SET << 1;
		public static final int SET_DIFFERENCE = INTERSECTION << 1;
		public static final int IS_IN = SET_DIFFERENCE << 1;
		public static final int NOT_IN = IS_IN << 1;
		public static final int SUBSET = NOT_IN << 1;
		public static final int SET_OP = SUCH_THAT | SEQUENCE | UNION | ELEMENT_UNION | POWER_SET | INTERSECTION
				| SET_DIFFERENCE | IS_IN | NOT_IN | SUBSET;

		// predicate operations
		public static final int CHOOSE = SUBSET << 1;
		public static final int FOR_ALL = CHOOSE << 1;
		public static final int EXISTS = FOR_ALL << 1; // 25 bits total

		// container tokens. we only need to know when we hit the start.
		// ( ) parens
		public static final int OPEN_PAREN = EXISTS << 1;
		// [ ] parens
		public static final int SQR_PAREN_O = OPEN_PAREN << 1;
		// { } parens
		public static final int CURLY_OPEN = SQR_PAREN_O << 1;
		// << >> parens
		public static final int ARROW_OPEN = CURLY_OPEN << 1; // 29

		public static final int CONTAINER_TOK = OPEN_PAREN | SQR_PAREN_O | CURLY_OPEN | ARROW_OPEN;

		// operators with 2 arguments on either side
		public static final int X_OP_X = (SIMPLE_ARITHMETIC | BOOL_OP | EXPONENT | STRING_APPEND | SET_OP)
				& ~(NEGATE | SUCH_THAT | ELEMENT_UNION | POWER_SET);
		// right side argument operators
		public static final int OP_X = NEGATE | ELEMENT_UNION | POWER_SET;

		private static final HashMap<String, Integer> tokenDict = new HashMap<String, Integer>() {
			{
				put("+", SIMPLE_ARITHMETIC);
				put("-", SIMPLE_ARITHMETIC);
				put("*", SIMPLE_ARITHMETIC);
				put("/", SIMPLE_ARITHMETIC);
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

				put("CHOOSE", CHOOSE);
				put("\\A", FOR_ALL);
				put("\\E", EXISTS);

				put("<<", ARROW_OPEN);
				put("{", CURLY_OPEN);
				put("[", SQR_PAREN_O);
				put("(", OPEN_PAREN);
				// TODO check http://lamport.azurewebsites.net/tla/p-manual.pdf
				// and
				// https://pdfs.semanticscholar.org/6ed6/404cc710511c2a77d190ff10f83e46324d91.pdf
				// for more tla expressions and support necessary ones.
				// pcal.PcalBuiltInSymbols has a whole list of stuff too
			}
		};

	}

	/*
	 * Maps a Dictionary bitmask to the corresponding operator precedence.
	 * Higher precedence => higher number.
	 * Operator precedence table found at http://lamport.azurewebsites.net/tla/summary-standalone.pdf
	 * TODO figure out precedence of operators not in table
	 */
	private static final HashMap<Integer, Integer> opPrecedence = new HashMap<Integer, Integer>() {
		{
			put(Dictionary.AND, 3);
			put(Dictionary.OR, 3);
			put(Dictionary.NEGATE, 4);
			put(Dictionary.NOT_EQ, 5);
			put(Dictionary.SMALLER, 5);
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
			put(Dictionary.SEQUENCE, 9);
			put(Dictionary.SIMPLE_ARITHMETIC, 13);
			put(Dictionary.STRING_APPEND, 13);
			put(Dictionary.EXPONENT, 14);
			put(Dictionary.OPEN_PAREN, 18);
			put(Dictionary.SQR_PAREN_O, 18);
			put(Dictionary.ARROW_OPEN, 18);
			put(Dictionary.CURLY_OPEN, 18);
		}
	};

	public Vector<PGoTLA> getResult() {
		return result;
	}
}
