package pgo.pcalparser;

import java.util.Vector;

/**
 * Tester class for the various annotations in pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class AnnotationTestParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("annotation with \\** before algorithm");
		v.add("annotation with (* *) before algorithm");
		v.add("annotation with other string in \\* comment");
		v.add("annotation with other string in (* *) comment");
		v.add("test }@Pgo }PGo @PGo @PGo} @PGo{ } @PGo still part of annotation");
		v.add("no space");
		v.add("many space");
		v.add("many per line1");
		v.add("more annote");
		v.add("multiline");
		v.add("more multiline");
		v.add("even more lines");
		v.add("annotation with \\** comment on code line");
		v.add("annotation with \\** on separate line");
		v.add("annotation with other string in \\* comment");
		v.add("still part of annotation");
		
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	protected String getAlg() {
		return "AnnotationTest";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
