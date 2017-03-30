package pgo.pcalparser;

import java.util.Vector;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class FastMutexPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("arg natural N numT");
		v.add("var x int");
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	protected String getAlg() {
		return "FastMutex";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
