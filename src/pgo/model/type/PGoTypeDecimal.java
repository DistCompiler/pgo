package pgo.model.type;

/**
 * Represents the floating point number type.
 */
public class PGoTypeDecimal extends PGoNumberType {
	private static final PGoTypeDecimal instance = new PGoTypeDecimal();
	private PGoTypeDecimal() {}
	public static PGoTypeDecimal getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Decimal";
	}

	@Override
	public String toGo() {
		return "float64";
	}

	@Override
	public int getSpecificity() {
		return 3;
	}
}
