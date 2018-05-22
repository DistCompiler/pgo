package pgo.model.pcal;

public abstract class NodeVisitor<T, E extends Throwable> {

	public abstract T visit(Algorithm algorithm) throws E;
	public abstract T visit(Processes processes) throws E;
	public abstract T visit(Statement statement) throws E;
	public abstract T visit(Label label) throws E;
	public abstract T visit(Macro macro) throws E;
	public abstract T visit(PcalProcess pcalProcess) throws E;
	public abstract T visit(Procedure procedure) throws E;
	public abstract T visit(VariableDecl variableDecl) throws E;

}
