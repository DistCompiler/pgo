package pgo.model.type;

/**
 * Represents sync.WaitGroup.
 */
public class PGoTypeWaitGroup extends PGoMiscellaneousType {
	private static final PGoTypeWaitGroup instance = new PGoTypeWaitGroup();
	private PGoTypeWaitGroup() {
		goType = "sync.WaitGroup";
	}
	public static PGoTypeWaitGroup getInstance() {
		return instance;
	}
}
