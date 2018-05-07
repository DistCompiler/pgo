package pgo.model.type;

/**
 * Represents the default integer type.
 */
public class PGoTypeError extends PGoPrimitiveType {
	private static final PGoTypeError instance = new PGoTypeError();
	private PGoTypeError() {}
	public static PGoTypeError getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Error";
	}

	@Override
	public String toGo() {
		return "error";
	}
}
