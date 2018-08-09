package pgo.model.pcal;

public abstract class PlusCalNodeVisitor<T, E extends Throwable> {

	public abstract T visit(PlusCalAlgorithm plusCalAlgorithm) throws E;
	public abstract T visit(PlusCalProcesses processes) throws E;
	public abstract T visit(PlusCalStatement statement) throws E;
	public abstract T visit(PlusCalLabel label) throws E;
	public abstract T visit(PlusCalMacro macro) throws E;
	public abstract T visit(PlusCalProcess plusCalProcess) throws E;
	public abstract T visit(PlusCalProcedure procedure) throws E;
	public abstract T visit(PlusCalVariableDeclaration variableDeclaration) throws E;
	public abstract T visit(PlusCalAssignmentPair plusCalAssignmentPair) throws E;

}
