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
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
}
