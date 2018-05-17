package pgo.model.type;

/**
 * Represents sync.RWMutex.
 */
public class PGoTypeRWMutex extends PGoMiscellaneousType {
	private static final PGoTypeRWMutex instance = new PGoTypeRWMutex();
	private PGoTypeRWMutex() {
		goType = "sync.RWMutex";
	}
	public static PGoTypeRWMutex getInstance() {
		return instance;
	}
}
