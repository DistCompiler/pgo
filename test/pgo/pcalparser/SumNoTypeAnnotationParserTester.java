package pgo.pcalparser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class SumNoTypeAnnotationParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		Vector<String> v = new Vector<String>();
		v.add("const uint64 MAXINT 10000000");
		v.add("arg uint64 RUNS runs");
		v.add("arg uint64 N numT");
		return v;
	}

	@Override
	public boolean expectException() {
		return false;
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
