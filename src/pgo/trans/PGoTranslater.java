package pgo.trans;

import pgo.pcalparser.PcalParser.ParsedPcal;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslater {
	
	// The pluscal AST to be translated
	private ParsedPcal pluscal;
	
	public PGoTranslater(ParsedPcal pcal) {
		this.pluscal = pcal;
	}
	
}
