package pgo.model.tla;

import java.util.List;

public class PGoTLASubstitutionKeyIndices extends PGoTLASubstitutionKey {

	private List<PGoTLAExpression> indices;

	public PGoTLASubstitutionKeyIndices(List<PGoTLAExpression> exprs) {
		this.indices = exprs;
	}
	
	public List<PGoTLAExpression> getIndices(){
		return indices;
	}

	@Override
	public <T> T accept(PGoTLASubstitutionKeyVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public String toString() {
		return "PGoTLASubstitutionKeyIndices [indices=" + indices + "]";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((indices == null) ? 0 : indices.hashCode());
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
		PGoTLASubstitutionKeyIndices other = (PGoTLASubstitutionKeyIndices) obj;
		if (indices == null) {
			if (other.indices != null)
				return false;
		} else if (!indices.equals(other.indices))
			return false;
		return true;
	}

}
