package pgo.model.pcal;

public abstract class ProcessesVisitor<T, E extends Throwable>{
	public abstract T visit(SingleProcess singleProcess) throws E;
	public abstract T visit(MultiProcess multiProcess) throws E;
}
