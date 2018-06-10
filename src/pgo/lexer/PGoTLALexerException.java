package pgo.lexer;

import java.util.List;

import pgo.PGoException;

public class PGoTLALexerException extends PGoException {

	public PGoTLALexerException(int lineN, String msg, List<TLAToken> tokensSoFar) {
		super("TLA Lexer error", msg, lineN);
	}

}
