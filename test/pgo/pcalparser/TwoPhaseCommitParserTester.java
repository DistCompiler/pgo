package pgo.pcalparser;

import java.util.Vector;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class TwoPhaseCommitParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("func void SetAll() string map[string]string");
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommit";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
