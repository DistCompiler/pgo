package pgo.model.pcal;

public abstract class PlusCalProcessesVisitor<T, E extends Throwable>{
	public abstract T visit(PlusCalSingleProcess singleProcess) throws E;
	public abstract T visit(PlusCalMultiProcess multiProcess) throws E;
}
