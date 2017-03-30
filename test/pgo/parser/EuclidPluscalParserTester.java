package pgo.parser;

import java.util.Vector;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class EuclidPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg int N", 6));
		v.add(new PGoAnnotation("var int u", 7));
		return v;
	}

	@Override
	protected String getAlg() {
		return "Euclid";
	}

}
