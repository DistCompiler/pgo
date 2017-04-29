package pgo.model.tla;

/**
 * Base TLA Expression representation
 *
 */
public abstract class PGoTLA {

	// the line number
	private int line;

	public PGoTLA(int line) {
		this.line = line;
	}

	public int getLine() {
		return line;
	}

	public static abstract class Walker<T> {
		// whether to terminate early
		protected boolean earlyTerm = false;
		protected T result;

		public Walker() {
			init();
		}

		protected abstract void init();

		public T getResult(PGoTLA ast) {
			walk(ast);
			return result;
		}

		private void walk(PGoTLA ast) {
			// TODO Auto-generated method stub

		}
	}
}
