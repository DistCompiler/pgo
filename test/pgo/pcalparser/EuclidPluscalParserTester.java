package pgo.pcalparser;

import java.util.Vector;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class EuclidPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("int N");
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	protected String getAlg() {
		return "Euclid";
	}

}
