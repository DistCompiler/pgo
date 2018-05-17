package pgo.model.type;

/**
 * Represents nothingness.
 */
public class PGoTypeVoid extends PGoPrimitiveType {
	private static final PGoTypeVoid instance = new PGoTypeVoid();
	private PGoTypeVoid() {}
	public static PGoTypeVoid getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Void";
	}

	@Override
	public String toGo() {
		// there is no void type in Go and returning an empty string is
		// perfectly valid
		return "";
	}
}
