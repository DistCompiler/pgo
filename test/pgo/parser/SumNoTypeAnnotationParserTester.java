package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class SumNoTypeAnnotationParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("const uint64 MAXINT 10000000", 8));
		v.add(new PGoAnnotation("arg uint64 RUNS runs", 9));
		v.add(new PGoAnnotation("arg uint64 N numT", 9));
		return v;
	}

	@Override
	protected String getAlg() {
		return "SumNoTypeAnnotation";
	}

	@Override
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + "Sum");
		return IOUtils.toString(inputStream);
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
