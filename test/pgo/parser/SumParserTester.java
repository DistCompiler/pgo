package pgo.parser;

import java.util.Vector;

import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class SumParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("const uint64 MAXINT 10000000", 8));
		v.add(new PGoAnnotation("arg uint64 RUNS runs", 9));
		v.add(new PGoAnnotation("arg uint64 N numT", 9));
		v.add(new PGoAnnotation("func SendTo() uint64t uint64t [](chan string)", 15));
		return v;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

}
