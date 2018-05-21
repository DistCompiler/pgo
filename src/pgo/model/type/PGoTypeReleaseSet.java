package pgo.model.type;

/**
 * Represents *distsys.ReleaseSet.
 */
public class PGoTypeReleaseSet extends PGoMiscellaneousType {
	private static final PGoTypeReleaseSet instance = new PGoTypeReleaseSet();
	private PGoTypeReleaseSet() {
		goType = "*distsys.ReleaseSet";
	}
	public static PGoTypeReleaseSet getInstance() {
		return instance;
	}
}
