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
	
	public String toTypeName() {
		return goType;
	}

}
