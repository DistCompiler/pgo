package pgo.model.golang;

/**
 * A label in Go. This will be on it's own line
 *
 */
public class Label extends Statement {

	private final String name;

	public Label(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

}
