package pgo.parser;

public class WhileParsingBuiltinToken extends ActionContext {

	private String token;

	public WhileParsingBuiltinToken(String token) {
		this.token = token;
	}

	public String getToken() {
		return token;
	}

	@Override
	public <T, E extends Throwable> T accept(ActionContextVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
