package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * PGo TLA AST:
 * 
 * CASE x -> y
 * 		[] z -> p
 * 		[] OTHER -> other
 *
 */
public class TLACase extends TLAExpression {

	private List<TLACaseArm> arms;
	private TLAExpression other;

	public TLACase(SourceLocation location, List<TLACaseArm> arms, TLAExpression other) {
		super(location);
		this.arms = arms;
		this.other = other;
	}
	
	@Override
	public TLACase copy() {
		return new TLACase(getLocation(), arms.stream().map(TLACaseArm::copy).collect(Collectors.toList()), other != null ? other.copy() : null);
	}
	
	public List<TLACaseArm> getArms(){
		return arms;
	}
	
	/**
	 * 
	 * @return the default expression for the case expression, null if there isn't one
	 */
	public TLAExpression getOther() {
		return other;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arms == null) ? 0 : arms.hashCode());
		result = prime * result + ((other == null) ? 0 : other.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TLACase other = (TLACase) obj;
		if (arms == null) {
			if (other.arms != null)
				return false;
		} else if (!arms.equals(other.arms))
			return false;
		if (this.other == null) {
			return other.other == null;
		} else return this.other.equals(other.other);
	}

}
