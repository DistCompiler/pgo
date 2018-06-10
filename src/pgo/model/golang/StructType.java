package pgo.model.golang;

import java.util.List;

public class StructType extends Type {

	private List<StructTypeField> fields;
	
	public StructType(List<StructTypeField> fields) {
		this.fields = fields;
	}
	
	public List<StructTypeField> getFields(){
		return fields;
	}
	
	@Override
	public <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E {
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
		StructType other = (StructType) obj;
		if (fields == null) {
			if (other.fields != null)
				return false;
		} else if (!fields.equals(other.fields))
			return false;
		return true;
	}

}
