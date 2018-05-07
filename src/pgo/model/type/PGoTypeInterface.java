package pgo.model.type;

/**
 * Represents the interface type.
 */
public class PGoTypeInterface extends PGoPrimitiveType {
	private static final PGoTypeInterface instance = new PGoTypeInterface();
	private PGoTypeInterface() {}
	public static PGoTypeInterface getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Interface";
	}

	@Override
	public String toGo() {
		return "interface{}";
	}
}
