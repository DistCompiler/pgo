package pgo.model.golang;

public class StringLiteral extends Expression {
	
	private String value;

	public StringLiteral(String value) {
		this.value = value;
	}
	
	public String getValue() {
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(ExpressionVisitor<T, E> visitor) throws E {
		return visitor.visit(this);
	}

	/*@Override
	public List<String> toGo() {
		StringBuilder out = new StringBuilder();
		// TODO: more correct string escaping
		out.append('"');
		for(int i = 0; i < value.length(); ++i) {
			char c = value.charAt(i);
			switch(c) {
				case '"':
					out.append("\\\"");
					break;
				default:
					out.append(c);
			}
		}
		out.append('"');
		return Collections.singletonList(out.toString());
	}*/

}
