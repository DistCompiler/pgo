package pgo.model.type;

import pgo.errors.IssueContext;

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

	public void harmonize(IssueContext ctx, PGoTypeConstraint constraint, PGoNumberType other) {
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
			ctx.error(new UnsatisfiableConstraintIssue(constraint, PGoTypeInt.getInstance(), PGoTypeDecimal.getInstance()));
			return;
		}
		num = higher;
		if (other instanceof PGoTypeUnrealizedNumber) {
			if (higher instanceof PGoTypeDecimal && ((PGoTypeUnrealizedNumber) other).isIntegralType) {
				ctx.error(new UnsatisfiableConstraintIssue(constraint, PGoTypeDecimal.getInstance(), PGoTypeInt.getInstance()));
				return;
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
	public PGoType realize(IssueContext ctx) {
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
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toGo() { throw new IllegalStateException("Trying to convert an unrealized number to Go"); }
}
