package pgo.trans;

import pgo.parser.PGoParseException;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.intermediate.PGoTransStageAtomicity;
import pgo.trans.intermediate.PGoTransStageOne;
import pgo.trans.intermediate.PGoTransStageType;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslater {
	
	// The pluscal AST to be translated
	private ParsedPcal pluscal;
	
	public PGoTranslater(ParsedPcal pcal) throws PGoTransException, PGoParseException {
		this.pluscal = pcal;
		PGoTransStageOne s1 = new PGoTransStageOne(pcal);
		PGoTransStageType s2 = new PGoTransStageType(s1);
		PGoTransStageAtomicity s3 = new PGoTransStageAtomicity(s2);
	}
	
}
