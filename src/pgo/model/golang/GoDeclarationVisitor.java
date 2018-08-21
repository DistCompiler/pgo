package pgo.model.golang;

public abstract class GoDeclarationVisitor<T, E extends Throwable> {

	public abstract T visit(GoFunctionDeclaration functionDeclaration) throws E;
	public abstract T visit(GoTypeDeclaration typeDeclaration) throws E;
	public abstract T visit(GoVariableDeclaration variableDeclaration) throws E;

}
