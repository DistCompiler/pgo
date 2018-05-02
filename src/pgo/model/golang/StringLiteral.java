package pgo.model.golang;

import java.util.Vector;

public class StringLiteral extends Expression {
	
	private String value;

	public StringLiteral(String value) {
		this.value = value;
	}

	@Override
	public Vector<String> toGo() {
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
		
		Vector<String> result = new Vector<>();
		result.add(out.toString());
		return result;
	}

}
