package pgo.model.type;

/**
 * Represents the default integer type.
 */
public class PGoTypeNatural extends PGoNumberType {
	private static final PGoTypeNatural instance = new PGoTypeNatural();
	private PGoTypeNatural() {}
	public static PGoTypeNatural getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "Natural";
	}

	@Override
	public String toGo() {
		return "uint64";
	}

	@Override
	public int getSpecificity() {
		return 1;
	}
}
