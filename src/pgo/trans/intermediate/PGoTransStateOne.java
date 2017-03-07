package pgo.trans.intermediate;

import pcal.AST;
import pgo.trans.PGoTransException;

/**
 * Makes initial pass over the AST to generate the basic intermediate
 * structures, which may not be fully populated (ie, type inference is not
 * completed).
 *
 */
public class PGoTransStateOne {

	// The PlusCal AST to parse
	private AST ast;

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	private boolean isMultiProcess;

	public PGoTransStateOne(AST ast) throws PGoTransException {
		this.ast = ast;
		trans();
	}

	public boolean getIsMultiProcess() {
		return isMultiProcess;
	}

	private void trans() throws PGoTransException {
		if (ast.MultiprocessObj == null) {
			if (ast.UniprocessObj == null) {
				throw new PGoTransException(
						"No PlusCal algorithm specified. PlusCal algorithm"
								+ " must either be multiprocess or uniprocess");
			}
			isMultiProcess = false;
		} else {
			if (ast.UniprocessObj != null) {
				throw new PGoTransException(
						"PlusCal algorithm specification error. "
								+ "Algorithm cannot be both multiprocess and uniprocess");
			}
			isMultiProcess = true;
		}
	}
}
