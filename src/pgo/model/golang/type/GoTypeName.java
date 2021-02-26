package pgo.model.golang.type;

public class GoTypeName extends GoType {
	
	private final String name;
	private final boolean builtin;
	
	public GoTypeName(String name) {
		this.name = name;
		this.builtin = false;
	}
	
	public GoTypeName(String name, boolean builtin) {
		this.name = name;
		this.builtin = builtin;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean isBuiltin() {
		return builtin;
	}
	
	@Override
	public <T, E extends Throwable> T accept(GoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
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
		GoTypeName other = (GoTypeName) obj;
		if (name == null) {
			return other.name == null;
		}
		return name.equals(other.name);
	}

}
