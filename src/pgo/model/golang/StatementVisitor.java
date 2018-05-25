package pgo.model.golang;

public abstract class StatementVisitor<T, E extends Throwable>{

	public abstract T visit(Comment comment) throws E;
	public abstract T visit(Assignment assignment) throws E;
	public abstract T visit(Return return1) throws E;
	public abstract T visit(Block block) throws E;
	public abstract T visit(For for1) throws E;
	public abstract T visit(If if1) throws E;
	public abstract T visit(Switch switch1) throws E;
	public abstract T visit(Label label) throws E;
	public abstract T visit(GoCall goCall) throws E;
	public abstract T visit(Select select) throws E;
	public abstract T visit(GoTo goTo) throws E;
	public abstract T visit(Expression expression) throws E;
	public abstract T visit(IncDec incDec) throws E;
	
}
