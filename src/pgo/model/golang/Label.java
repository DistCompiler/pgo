package pgo.model.golang;

/**
 * A label in Go. This will be on it's own line
 *
 */
public class Label extends Statement {

	private String name;

	public Label(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public <T, E extends Throwable> T accept(StatementVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
