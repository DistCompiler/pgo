package pgo.model.golang;

public abstract class NodeVisitor<T, E extends Throwable> {

	public abstract T visit(Module module) throws E;
	public abstract T visit(Statement statement) throws E;
	public abstract T visit(Declaration declaration) throws E;
	public abstract T visit(Type type) throws E;
	public abstract T visit(StructTypeField structTypeField) throws E;
	public abstract T visit(SwitchCase switchCase) throws E;
	public abstract T visit(LabelName labelName) throws E;
	public abstract T visit(FunctionArgument functionArgument) throws E;
	public abstract T visit(Expression expression) throws E;
	public abstract T visit(InterfaceTypeField interfaceTypeField) throws E;

}
