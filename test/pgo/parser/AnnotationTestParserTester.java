package pgo.parser;

import java.util.Vector;

import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the various annotations in pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class AnnotationTestParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("annotation with \\** before algorithm", 6));
		v.add(new PGoAnnotation("annotation with (* *) before algorithm", 7));
		v.add(new PGoAnnotation("annotation with other string in \\* comment", 8));
		v.add(new PGoAnnotation("annotation with other string in (* *) comment", 9));
		v.add(new PGoAnnotation("test }@Pgo }PGo @PGo @PGo} @PGo{ } @PGo still part of annotation",11));
		v.add(new PGoAnnotation("no space",12));
		v.add(new PGoAnnotation("many space",13));
		v.add(new PGoAnnotation("many per line1",14));
		v.add(new PGoAnnotation("more annote",14));
		v.add(new PGoAnnotation("multiline",15));
		v.add(new PGoAnnotation("more multiline",15));
		v.add(new PGoAnnotation("even more lines",17));
		v.add(new PGoAnnotation("annotation with \\** comment on code line",21));
		v.add(new PGoAnnotation("annotation with \\** on separate line",22));
		v.add(new PGoAnnotation("annotation with other string in \\* comment",23));
		v.add(new PGoAnnotation("still part of annotation", 29));
		
		return v;
	}

	@Override
	protected String getAlg() {
		return "annotationtests/AnnotationTest";
	}

}
