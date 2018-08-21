package pgo.model.golang;

public abstract class GoStatementVisitor<T, E extends Throwable>{

	public abstract T visit(GoComment comment) throws E;
	public abstract T visit(GoAssignmentStatement assignment) throws E;
	public abstract T visit(GoReturn goReturn) throws E;
	public abstract T visit(GoBlock block) throws E;
	public abstract T visit(GoFor goFor) throws E;
	public abstract T visit(GoForRange forRange) throws E;
	public abstract T visit(GoIf goIf) throws E;
	public abstract T visit(GoSwitch goSwitch) throws E;
	public abstract T visit(GoLabel label) throws E;
	public abstract T visit(GoSelect select) throws E;
	public abstract T visit(GoTo goTo) throws E;
	public abstract T visit(GoIncDec incDec) throws E;
	public abstract T visit(GoExpressionStatement expressionStatement) throws E;
	public abstract T visit(GoBreak break1) throws E;
	public abstract T visit(GoContinue continue1) throws E;
	public abstract T visit(GoDefer defer) throws E;
	public abstract T visit(GoRoutineStatement go) throws E;
	public abstract T visit(GoVariableDeclarationStatement variableDeclarationStatement) throws E;

}
