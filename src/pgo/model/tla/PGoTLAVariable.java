package pgo.model.tla;

/**
 * Variable access in TLA Expr
 *
 */
public class PGoTLAVariable extends PGoTLA {

	private String name;

	public PGoTLAVariable(String n, int line) {
		super(line);
		name = n;
	}

	public String getName() {
		return name;
	}
}
