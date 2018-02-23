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

	public static class PGoNetCentralizedState extends PGoMiscellaneousType {
		public PGoNetCentralizedState() { this.goType = "*distsys.CentralizedState"; }
	}

	public static class PGoNetConfig extends PGoMiscellaneousType {
		public PGoNetConfig() { this.goType = "distsys.Config"; }
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
		case "distsys.CentralizedState":
			return new PGoNetCentralizedState();
		case "distsys.Config":
			return new PGoNetConfig();
		}
		return PGoType.UNDETERMINED;
	}

}
