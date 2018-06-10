package pgo;

public class InternalCompilerError extends RuntimeException {
	public InternalCompilerError() {
		super("internal compiler error");
	}

	public InternalCompilerError(Exception e) {
		super("internal compiler error", e);
	}
}
