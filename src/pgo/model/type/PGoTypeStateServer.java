package pgo.model.type;

/**
 * Represents distsys.StateServer.
 */
public class PGoTypeStateServer extends PGoMiscellaneousType {
	private static final PGoTypeStateServer instance = new PGoTypeStateServer();
	private PGoTypeStateServer() {
		goType = "distsys.StateServer";
	}
	public static PGoTypeStateServer getInstance() {
		return instance;
	}
}
