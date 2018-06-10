package pgo.model.golang;

public abstract class Type extends Node {
	
	@Override
	public abstract int hashCode();
	
	@Override
	public abstract boolean equals(Object other);
	
	public abstract <T, E extends Throwable> T accept(TypeVisitor<T, E> v) throws E;
	
	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
