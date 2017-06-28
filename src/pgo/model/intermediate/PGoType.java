package pgo.model.intermediate;

/**
 * Base class representing all types in pluscal and go
 *
 */
public abstract class PGoType {

	// void type
	public static final PGoType VOID = PGoPrimitiveType.inferPrimitiveFromGoTypeName("void");

	public static final PGoType UNDETERMINED = new PGoType.PGoUndetermined();

	// whether this type is determinable
	protected boolean isUndetermined = false;
	// whether the type contains template arguments
	protected boolean hasTemplateArgs = false;

	/**
	 * Attempts to infer the type from the given pluscal expressions
	 * 
	 * @return a PGoType of inferred type
	 */
	public static PGoType inferFromGoTypeName(String s) {
		PGoType r = PGoPrimitiveType.inferPrimitiveFromGoTypeName(s);
		if (r.isUndetermined()) {
			r = PGoCollectionType.inferContainerFromGoTypeName(s);
		}
		return r;
	}

	/**
	 * 
	 * @return whether the type is undetermined
	 */
	public boolean isUndetermined() {
		return isUndetermined;
	}
	
	/**
	 * 
	 * @return whether the type contains template args
	 */
	public boolean hasTemplateArgs() {
		return hasTemplateArgs;
	}

	/**
	 * 
	 * @return the type name
	 */
	public abstract String toTypeName();

	/**
	 * Represents an indeterminable type
	 *
	 */
	public static class PGoUndetermined extends PGoType {

		public PGoUndetermined() {
			isUndetermined = true;
		}

		@Override
		public String toTypeName() {
			return "";
		}

	}

	@Override
	public boolean equals(Object p) {
		if (p == null) {
			return false;
		}
		if (!(p instanceof PGoType)) {
			return false;
		}
		PGoType op = (PGoType) p;
		return toTypeName().equals(op.toTypeName());
	}

	@Override
	public int hashCode() {
		return this.toTypeName().hashCode();
	}

	/**
	 * Converts to the go code syntax of this type
	 * 
	 * @return
	 */
	public String toGo() {
		return toTypeName();
	}

}
