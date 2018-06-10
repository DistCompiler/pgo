package pgo.model.golang;

public abstract class DeclarationVisitor<T, E extends Throwable> {

	public abstract T visit(FunctionDeclaration functionDeclaration) throws E;
	public abstract T visit(TypeDeclaration typeDeclaration) throws E;
	public abstract T visit(VariableDeclaration variableDeclaration) throws E;

}
