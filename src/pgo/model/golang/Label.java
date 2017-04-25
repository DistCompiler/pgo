package pgo.model.golang;

/**
 * A label in Go. This will be on it's own line
 *
 */
public class Label extends Expression {

	private final String labelName;

	public Label(String name) {
		labelName = name;
	}

	public String getLabelName() {
		return labelName;
	}

	@Override
	public String toGoExpr() {
		return labelName + ":";
	}

}
