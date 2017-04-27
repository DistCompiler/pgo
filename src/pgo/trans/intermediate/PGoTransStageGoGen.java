package pgo.trans.intermediate;

import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;

/**
 * The last stage of the translation. Takes given intermediate data and converts
 * it to a Go AST, properly
 *
 */
public class PGoTransStageGoGen extends PGoTransStageBase {

	public PGoTransStageGoGen(PGoTransStageAtomicity s1) throws PGoParseException, PGoTransException {
		super(s1);
	}

}
