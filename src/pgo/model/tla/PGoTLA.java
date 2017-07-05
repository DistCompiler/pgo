package pgo.model.tla;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

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

	/**
	 * Convert the TLA expression into its GoAST representation using the
	 * translator passed in.
	 * 
	 * @throws PGoTransException
	 *             if there is a type contradiction
	 */
	protected abstract Expression convert(TLAExprToGo trans) throws PGoTransException;

	/**
	 * Infer the type of the TLA expression using the translator passed in.
	 * 
	 * @throws PGoTransException
	 *             if there is a type contradiction
	 */
	protected abstract PGoType inferType(TLAExprToType trans) throws PGoTransException;

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
			// TODO (issue #9) Auto-generated method stub

		}
	}
}
