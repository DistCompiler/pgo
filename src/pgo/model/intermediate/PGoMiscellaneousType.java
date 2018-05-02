package pgo.model.intermediate;

/**
 * Contains some miscellaneous Go types that we might use in compilation.
 *
 */
public abstract class PGoMiscellaneousType extends PGoType {

	protected String goType;

	public static class PGoWaitGroup extends PGoMiscellaneousType {
		public PGoWaitGroup() {
			this.goType = "sync.WaitGroup";
		}
	}

	public static class PGoRWMutex extends PGoMiscellaneousType {
		public PGoRWMutex() {
			this.goType = "sync.RWMutex";
		}
	}

	public static class EtcdState extends PGoMiscellaneousType {
		public EtcdState() { this.goType = "*distsys.EtcdState"; }
	}

	public static class State extends PGoMiscellaneousType {
		public State() { this.goType = "distsys.State"; }
	}

	public static class PGoNetConfig extends PGoMiscellaneousType {
		public PGoNetConfig() { this.goType = "distsys.Config"; }
	}

	public static class StateServer extends PGoMiscellaneousType {
		public StateServer() { this.goType = "distsys.StateServer"; }
	}

	public static class StateServerReleaseSet extends PGoMiscellaneousType {
		public StateServerReleaseSet() { this.goType = "*distsys.ReleaseSet"; }
	}

	public static class StateServerAcquireSet extends PGoMiscellaneousType {
		public StateServerAcquireSet() { this.goType = "distsys.AcquireSet"; }
	}

	public static class StateServerValueMap extends PGoMiscellaneousType {
		public StateServerValueMap() { this.goType = "map[string]interface{}"; }
	}

	@Override
	public String toTypeName() {
		return goType;
	}

	public static PGoType inferMiscFromGoTypeName(String s) {
		switch (s) {
		case "sync.WaitGroup":
			return new PGoWaitGroup();
		case "sync.RWMutex":
			return new PGoRWMutex();
		case "distsys.EtcdState":
			return new EtcdState();
		case "distsys.Config":
			return new PGoNetConfig();
		case "distsys.StateServer":
			return new StateServer();
		}
		return PGoType.UNDETERMINED;
	}

}
