package pgo.model.type;

/**
 * Represents *distsys.EtcdState.
 */
public class PGoTypeEtcdState extends PGoMiscellaneousType {
	private static final PGoTypeEtcdState instance = new PGoTypeEtcdState();
	private PGoTypeEtcdState() {
		goType = "distsys.EtcdState";
	}
	public static PGoTypeEtcdState getInstance() {
		return instance;
	}
}
