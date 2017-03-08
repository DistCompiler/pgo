package pgo.trans.intermediate;

import pcal.AST;
import pcal.AST.Multiprocess;
import pcal.AST.Uniprocess;
import pgo.trans.PGoTransException;

/**
 * Makes initial pass over the AST to generate the basic intermediate
 * structures, which may not be fully populated (ie, type inference is not
 * completed).
 *
 */
public class PGoTransStageOne {

	// The PlusCal AST to parse
	private AST ast;

	// Whether the PlusCal program has multiple processes, or is just a single
	// threaded function
	private boolean isMultiProcess;

	public PGoTransStageOne(AST ast) throws PGoTransException {
		this.ast = ast;
		trans();
	}

	public boolean getIsMultiProcess() {
		return isMultiProcess;
	}

	/**
	 * Translates the PlusCal AST to the first stage intermediate representation
	 * 
	 * @throws PGoTransException
	 *             on error
	 */
	private void trans() throws PGoTransException {
		if (ast instanceof Uniprocess) {
			isMultiProcess = false;
			trans((Uniprocess) ast);
		} else if (ast instanceof Multiprocess) {
			isMultiProcess = true;
			trans((Multiprocess) ast);
		} else {
			throw new PGoTransException("Error: PlusCal algorithm must be one of" + " uniprocess or multiprocess");
		}
	}

	private void trans(Multiprocess ast) {
		// TODO Auto-generated method stub

	}

	private void trans(Uniprocess ast) {
		// TODO Auto-generated method stub

	}
}
