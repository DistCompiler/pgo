package pgo.model.type;

/**
 * Represents the string type.
 */
public class PGoTypeString extends PGoPrimitiveType {
	private static final PGoTypeString instance = new PGoTypeString();
	private PGoTypeString() {}
	public static PGoTypeString getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "String";
	}

	@Override
	public String toGo() {
		return "string";
	}
}
