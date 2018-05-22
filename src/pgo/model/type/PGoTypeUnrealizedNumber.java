package pgo.model.type;

/**
 * Implements promotion for number types.
 */
public class PGoTypeUnrealizedNumber extends PGoNumberType {
	private PGoNumberType num;
	private boolean isIntegralType;

	public PGoTypeUnrealizedNumber() {
		this(PGoTypeNatural.getInstance());
	}

	public PGoTypeUnrealizedNumber(PGoTypeNatural num) {
		this.num = num;
	}

	public PGoTypeUnrealizedNumber(PGoTypeInt num) {
		this.num = num;
	}

	public PGoTypeUnrealizedNumber(PGoTypeDecimal num) {
		this.num = num;
	}

	public static PGoTypeUnrealizedNumber integralType() {
		PGoTypeUnrealizedNumber t = new PGoTypeUnrealizedNumber();
		t.isIntegralType = true;
		return t;
	}

	public void harmonize(PGoNumberType other) {
		int mySpecificity = num.getSpecificity();
		int otherSpecificity = other.getSpecificity();
		PGoNumberType otherNum = other;
		if (other instanceof PGoTypeUnrealizedNumber) {
			otherNum = ((PGoTypeUnrealizedNumber) other).num;
		}
		PGoNumberType higher = num;
		if (mySpecificity < otherSpecificity) {
			higher = otherNum;
		}
		if (higher instanceof PGoTypeDecimal && isIntegralType) {
			throw new PGoTypeUnificationException(PGoTypeInt.getInstance(), PGoTypeDecimal.getInstance());
		}
		num = higher;
		if (other instanceof PGoTypeUnrealizedNumber) {
			if (((PGoTypeUnrealizedNumber) other).isIntegralType) {
				throw new PGoTypeUnificationException(PGoTypeInt.getInstance(), PGoTypeDecimal.getInstance());
			}
			((PGoTypeUnrealizedNumber) other).num = higher;
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof PGoTypeUnrealizedNumber)) {
			return false;
		}
		return num.equals(((PGoTypeUnrealizedNumber) obj).num);
	}

	@Override
	public PGoType realize() {
		return num;
	}

	@Override
	public int getSpecificity() {
		return num.getSpecificity();
	}

	@Override
	public String toTypeName() {
		return "UnrealizedNumber[" + num.toTypeName() + "]";
	}

	@Override
	public String toGo() { throw new IllegalStateException("Trying to convert an unrealized number to Go"); }
}
