package pgo.model.golang;

public abstract class GoDeclaration extends GoNode {

	@Override
	public <T, E extends Throwable> T accept(GoNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}
	
	public abstract <T, E extends Throwable> T accept(GoDeclarationVisitor<T, E> v) throws E;

}
