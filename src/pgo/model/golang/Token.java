package pgo.model.golang;

/**
 * Special go tokens. These are symbols, like arithmetic operators, channel
 * accessors, or literals (int, strings)
 *
 */
public class Token extends Expression {

	private final String token;

	public Token(String t) {
		token = t;
	}

	public String getToken() {
		return token;
	}

	@Override
	public String toGoExpr() {
		return token;
	}

}
