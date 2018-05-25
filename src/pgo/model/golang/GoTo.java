package pgo.model.golang;

/**
 * A Goto in pluscal and go
 *
 */
public class GoTo extends Statement {
	// the to label location
	private LabelName to;

	public GoTo(LabelName to) {
		this.to = to;
	}

	public LabelName getTo() {
		return to;
	}
	
	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
