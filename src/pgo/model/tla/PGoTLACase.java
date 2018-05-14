package pgo.model.tla;

import java.util.List;

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
public class PGoTLACase extends PGoTLAExpression {

	private List<PGoTLACaseArm> arms;
	private PGoTLAExpression other;

	public PGoTLACase(SourceLocation location, List<PGoTLACaseArm> arms, PGoTLAExpression other) {
		super(location);
		this.arms = arms;
		this.other = other;
	}
	
	public List<PGoTLACaseArm> getArms(){
		return arms;
	}
	
	/**
	 * 
	 * @return the default expression for the case expression, null if there isn't one
	 */
	public PGoTLAExpression getOther() {
		return other;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLACase other = (PGoTLACase) obj;
		if (arms == null) {
			if (other.arms != null)
				return false;
		} else if (!arms.equals(other.arms))
			return false;
		if (this.other == null) {
			if (other.other != null)
				return false;
		} else if (!this.other.equals(other.other))
			return false;
		return true;
	}

}
