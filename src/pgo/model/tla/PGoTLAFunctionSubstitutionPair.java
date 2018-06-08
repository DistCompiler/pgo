package pgo.model.tla;

import java.util.List;

public class PGoTLAFunctionSubstitutionPair {

	private List<PGoTLASubstitutionKey> keys;
	private PGoTLAExpression value;

	public PGoTLAFunctionSubstitutionPair(List<PGoTLASubstitutionKey> keys, PGoTLAExpression value) {
		this.keys = keys;
		this.value = value;
	}
	
	public List<PGoTLASubstitutionKey> getKeys(){
		return keys;
	}
	
	public PGoTLAExpression getValue() {
		return value;
	}

	@Override
	public String toString() {
		return "PGoTLAFunctionSubstitutionPair [keys=" + keys + ", value=" + value + "]";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((keys == null) ? 0 : keys.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
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
		PGoTLAFunctionSubstitutionPair other = (PGoTLAFunctionSubstitutionPair) obj;
		if (keys == null) {
			if (other.keys != null)
				return false;
		} else if (!keys.equals(other.keys))
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
