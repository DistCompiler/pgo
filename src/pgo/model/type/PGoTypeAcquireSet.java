package pgo.model.type;

/**
 * Represents distsys.AcquireSet.
 */
public class PGoTypeAcquireSet extends PGoMiscellaneousType {
	private static final PGoTypeAcquireSet instance = new PGoTypeAcquireSet();
	private PGoTypeAcquireSet() {
		goType = "distsys.AcquireSet";
	}
	public static PGoTypeAcquireSet getInstance() {
		return instance;
	}
}
