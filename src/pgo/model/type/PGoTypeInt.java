package pgo.model.type;

/**
 * Represents a fallback integer type.
 */
public class PGoTypeInt extends PGoNumberType {
	private static final PGoTypeInt instance = new PGoTypeInt();
	private PGoTypeInt() {}
	public static PGoTypeInt getInstance() {
		 return instance;
	}

	@Override
	public String toTypeName() {
		return "Int";
	}

	@Override
	public String toGo() {
		return "int";
	}

	@Override
	public int getSpecificity() {
		return 2;
	}
}
