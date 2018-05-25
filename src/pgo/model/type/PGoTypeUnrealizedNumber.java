package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Implements promotion for number types.
 */
public class PGoTypeUnrealizedNumber extends PGoNumberType {
	private PGoNumberType num;
	private boolean isIntegralType;

	public PGoTypeUnrealizedNumber(PGoTypeNatural num, Origin... origins) {
		this(num, Arrays.asList(origins));
	}

	public PGoTypeUnrealizedNumber(PGoTypeNatural num, List<Origin> origins) {
		super(origins);
		this.num = num;
	}

	public PGoTypeUnrealizedNumber(PGoTypeInt num, Origin... origins) {
		this(num, Arrays.asList(origins));
	}

	public PGoTypeUnrealizedNumber(PGoTypeInt num, List<Origin> origins) {
		super(origins);
		this.num = num;
	}

	public static PGoTypeUnrealizedNumber integralType(Origin... origins) {
		return integralType(Arrays.asList(origins));
	}

	public static PGoTypeUnrealizedNumber integralType(List<Origin> origins) {
		PGoTypeUnrealizedNumber t = new PGoTypeUnrealizedNumber(new PGoTypeNatural(origins), origins);
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
			ctx.error(new UnsatisfiableConstraintIssue(constraint, num, higher));
			return;
		}
		num = higher;
		if (other instanceof PGoTypeUnrealizedNumber) {
			if (higher instanceof PGoTypeDecimal && ((PGoTypeUnrealizedNumber) other).isIntegralType) {
				ctx.error(new UnsatisfiableConstraintIssue(constraint, higher, ((PGoTypeUnrealizedNumber) other).num));
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
		return num.copyWithOrigins(getOrigins());
	}

	@Override
	public int getSpecificity() {
		return num.getSpecificity();
	}

	@Override
	public PGoNumberType copyWithOrigins(List<Origin> origins) {
		throw new IllegalStateException("internal compiler error");
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
