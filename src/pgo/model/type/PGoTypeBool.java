package pgo.model.type;

/**
 * Represents the boolean type.
 */
public class PGoTypeBool extends PGoPrimitiveType {
	private static final PGoTypeBool instance = new PGoTypeBool();
	private PGoTypeBool() {}
	public static PGoTypeBool getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Bool";
	}

	@Override
	public String toGo() {
		return "bool";
	}
}
