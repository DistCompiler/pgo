package pgo.model.tla;

public class PGoTLASubstitutionKeyName extends PGoTLASubstitutionKey {

	private String name;

	public PGoTLASubstitutionKeyName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}

	@Override
	public <T> T accept(PGoTLASubstitutionKeyVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public String toString() {
		return "PGoTLASubstitutionKeyName [name=" + name + "]";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		PGoTLASubstitutionKeyName other = (PGoTLASubstitutionKeyName) obj;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}

}
