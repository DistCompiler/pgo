package pgo.model.golang;

/**
 * A Goto in pluscal and go
 *
 */
public class GoTo extends Expression {
	// the to label location
	private LabelName to;

	public GoTo(LabelName to) {
		this.to = to;
	}

	public LabelName getTo() {
		return to;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}
}
