package pgo.model.golang;

import java.util.List;

/**
 * A return keyword in go
 *
 */
public class Return extends Statement {

	// the return value if any
	private List<Expression> values;

	public Return(List<Expression> values) {
		this.values = values;
	}

	public List<Expression> getValues() {
		return values;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

}
