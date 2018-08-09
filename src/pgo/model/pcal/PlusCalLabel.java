package pgo.model.pcal;

import pgo.util.SourceLocation;

public class PlusCalLabel extends PlusCalNode {
	String name;
	Modifier modifier;
	
	public static enum Modifier{
		PLUS,
		MINUS,
		NONE,
	}
	
	public PlusCalLabel(SourceLocation location, String name, Modifier modifier) {
		super(location);
		this.name = name;
		this.modifier = modifier;
	}
	
	@Override
	public PlusCalLabel copy() {
		return new PlusCalLabel(getLocation(), name, modifier);
	}
	
	public String getName() {
		return name;
	}
	
	public Modifier getModifier() {
		return modifier;
	}
	
	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((modifier == null) ? 0 : modifier.hashCode());
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
		PlusCalLabel other = (PlusCalLabel) obj;
		if (modifier != other.modifier)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}
}
