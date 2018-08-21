package pgo.model.golang.type;

import java.util.List;

public class GoStructType extends GoType {

	private List<GoStructTypeField> fields;
	
	public GoStructType(List<GoStructTypeField> fields) {
		this.fields = fields;
	}
	
	public List<GoStructTypeField> getFields(){
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
		GoStructType other = (GoStructType) obj;
		if (fields == null) {
			return other.fields == null;
		} else return fields.equals(other.fields);
	}

}
