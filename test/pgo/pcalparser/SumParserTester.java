package pgo.pcalparser;

import java.util.Vector;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class SumParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("const uint64 MAXINT 10000000");
		v.add("arg uint64 RUNS runs");
		v.add("arg uint64 N numT");
		v.add("func SendTo() uint64t uint64t [](chan string)");
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
