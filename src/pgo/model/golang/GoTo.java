package pgo.model.golang;

/**
 * A Goto in pluscal and go
 *
 */
public class GoTo extends Expression {
	// the to lable location
	private String to;

	public GoTo(String to) {
		this.to = to;
	}

	public String getTo() {
		return to;
	}

	public void setTo(String to) {
		this.to = to;
	}

	@Override
	public String toGoExpr() {
		return "goto " + to;
	}
}
