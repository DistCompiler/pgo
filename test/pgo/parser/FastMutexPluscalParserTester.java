package pgo.parser;

import java.util.Vector;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class FastMutexPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg natural N numT", 6));
		v.add(new PGoAnnotation("var x int", 8));
		return v;
	}

	@Override
	protected String getAlg() {
		return "FastMutex";
	}

}
