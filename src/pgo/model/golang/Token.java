package pgo.model.golang;

import java.util.Collections;
import java.util.List;

/**
 * A tokens such as "var[2]".
 */
public class Token extends Expression {

	// the tokens in this expression
	private String toks;

	public Token(String tok) {
		this.toks = tok;
	}

	public String getTokens() {
		return this.toks;
	}

	public void setExpressions(String exps) {
		this.toks = exps;
	}

	public void merge(Token t) {
		toks = toks + t.toks;
	}

	@Override
	public List<String> toGo() {
		return Collections.singletonList(toks);
	}

}
