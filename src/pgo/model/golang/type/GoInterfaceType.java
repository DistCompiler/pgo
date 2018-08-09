package pgo.model.golang.type;

import java.util.List;

public class GoInterfaceType extends GoType {
	
	private List<GoInterfaceTypeField> fields;

	public GoInterfaceType(List<GoInterfaceTypeField> fields) {
		this.fields = fields;
	}

	public List<GoInterfaceTypeField> getFields() {
		return fields;
	}

	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fields == null) ? 0 : fields.hashCode());
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
		GoInterfaceType other = (GoInterfaceType) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
