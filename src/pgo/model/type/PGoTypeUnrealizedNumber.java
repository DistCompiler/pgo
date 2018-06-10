package pgo.model.type;

import pgo.InternalCompilerError;
import pgo.errors.Issue;
import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

/**
 * Implements promotion for number types.
 */
public class PGoTypeUnrealizedNumber extends PGoNumberType {
	private PGoNumberType num;

	public PGoTypeUnrealizedNumber(PGoTypeInt num, List<Origin> origins) {
		this((PGoNumberType) num, origins);
	}

	private PGoTypeUnrealizedNumber(PGoNumberType num, List<Origin> origins) {
		super(origins);
		this.num = num;
	}

	public Optional<Issue> harmonize(PGoNumberType other) {
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
		num = higher;
		if (other instanceof PGoTypeUnrealizedNumber) {
			((PGoTypeUnrealizedNumber) other).num = higher;
		}
		return Optional.empty();
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
		throw new InternalCompilerError();
	}

	@Override
	public String toTypeName() {
		return "UnrealizedNumber[" + num.toTypeName() + "]";
	}

	@Override
	public PGoType copy() {
		return new PGoTypeUnrealizedNumber(num, getOrigins());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
