package pgo.model.golang;

import java.util.Collections;
import java.util.List;

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
	public List<String> toGo() {
		return Collections.singletonList(labelName + ":");
	}

}
