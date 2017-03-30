package pgo.parser;

import java.util.Vector;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the Queens pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class QueensPluscalProcedureParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg int N", 45));
		v.add(new PGoAnnotation("return rVal", 49));
		return v;
	}

	@Override
	protected String getAlg() {
		return "QueensPluscalProcedure";
	}

}
