package pgo.model.type;

/**
 * Represents a process ID argument.
 *
 * FIXME this is a hack
 */
public class PGoTypeProcessId extends PGoPrimitiveType {
	private static final PGoTypeProcessId instance = new PGoTypeProcessId();
	private PGoTypeProcessId() {}
	public static PGoTypeProcessId getInstance() {
		return instance;
	}

	@Override
	public String toTypeName() {
		return "ProcessId";
	}

	@Override
	public String toGo() {
		throw new RuntimeException("Trying to convert process ID type to Go");
	}
}
