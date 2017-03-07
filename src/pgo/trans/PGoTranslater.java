package pgo.trans;

import pcal.AST;

/**
 * Performs the translation of the PlusCal AST into a Golang AST
 * 
 */
public class PGoTranslater {
	
	// The pluscal AST to be translated
	private AST pluscal;
	
	public PGoTranslater(AST pluscal) {
		this.pluscal = pluscal;
	}
	
}
