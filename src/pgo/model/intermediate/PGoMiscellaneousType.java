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

	public static class PGoNetGlobalState extends PGoMiscellaneousType {
		public PGoNetGlobalState() { this.goType = "*pgonet.GlobalState"; }
	}

	public static class PGoNetConfig extends PGoMiscellaneousType {
		public PGoNetConfig() { this.goType = "pgonet.Config"; }
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
		case "pgonet.GlobalState":
			return new PGoNetGlobalState();
		case "pgonet.Config":
			return new PGoNetConfig();
		}
		return PGoType.UNDETERMINED;
	}

}
