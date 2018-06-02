package pgo;

public class Unreachable extends RuntimeException {
	public Unreachable() {
		super("unreachable");
	}

	public Unreachable(Exception e) {
		super("unreachable", e);
	}
}
