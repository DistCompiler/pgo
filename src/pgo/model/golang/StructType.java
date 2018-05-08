package pgo.model.golang;

import java.util.List;

public class StructType extends Type {
	
	public static class StructField{
		String name;
		Type type;
		
		public StructField(String name, Type type) {
			this.name = name;
			this.type = type;
		}
		
		public String getName() {
			return name;
		}
		
		public Type getType() {
			return type;
		}
	}

	private List<StructField> fields;
	
	public StructType(List<StructField> fields) {
		this.fields = fields;
	}
	
	public List<StructField> getFields(){
		return fields;
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
