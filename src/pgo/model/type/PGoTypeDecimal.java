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
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int getSpecificity() {
		return 3;
	}
}
