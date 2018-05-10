package pgo.model.pcal;

import java.util.List;

import pgo.util.SourceLocation;

public class Either extends Statement {

	List<List<Statement>> cases;
	
	public Either(SourceLocation location, List<List<Statement>> cases) {
		super(location);
		this.cases = cases;
	}
	
	public List<List<Statement>> getCases(){
		return cases;
	}
	
	@Override
	public <T> T accept(Visitor<T> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((cases == null) ? 0 : cases.hashCode());
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
		Either other = (Either) obj;
		if (cases == null) {
			if (other.cases != null)
				return false;
		} else if (!cases.equals(other.cases))
			return false;
		return true;
	}

}
