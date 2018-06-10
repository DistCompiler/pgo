package pgo.model.pcal;

public abstract class StatementVisitor<T, E extends Throwable>{
	public abstract T visit(LabeledStatements labeledStatements) throws E;
	public abstract T visit(While while1) throws E;
	public abstract T visit(If if1) throws E;
	public abstract T visit(Either either) throws E;
	public abstract T visit(Assignment assignment) throws E;
	public abstract T visit(Return return1) throws E;
	public abstract T visit(Skip skip) throws E;
	public abstract T visit(Call call) throws E;
	public abstract T visit(MacroCall macroCall) throws E;
	public abstract T visit(With with) throws E;
	public abstract T visit(Print print) throws E;
	public abstract T visit(Assert assert1) throws E;
	public abstract T visit(Await await) throws E;
	public abstract T visit(Goto goto1) throws E;
}
