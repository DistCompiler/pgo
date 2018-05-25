package pgo.model.golang;

public abstract class Declaration extends Node {

	@Override
	public <T, E extends Throwable> T accept(NodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(DeclarationVisitor<T, E> v) throws E;

}
