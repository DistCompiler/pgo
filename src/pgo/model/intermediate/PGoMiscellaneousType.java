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

	public static class CentralizedState extends PGoMiscellaneousType {
		public CentralizedState() { this.goType = "*distsys.CentralizedState"; }
	}

	public static class State extends PGoMiscellaneousType {
		public State() { this.goType = "distsys.State"; }
	}

	public static class PGoNetConfig extends PGoMiscellaneousType {
		public PGoNetConfig() { this.goType = "distsys.Config"; }
	}
	
	public static class DosLib extends PGoMiscellaneousType {
		public DosLib() { this.goType = "doslib.DOS"; }
	}
	
	public static class DosLibReleaseSet extends PGoMiscellaneousType {
		public DosLibReleaseSet() { this.goType = "*doslib.ReleaseSet"; }
	}
	
	public static class DosLibAcquireSet extends PGoMiscellaneousType {
		public DosLibAcquireSet() { this.goType = "doslib.AcquireSet"; }
	}
	
	public static class DosLibValueMap extends PGoMiscellaneousType {
		public DosLibValueMap() { this.goType = "map[string]interface{}"; }
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
		case "doslib.DOS":
			return new DosLib();
		}
		return PGoType.UNDETERMINED;
	}

}
