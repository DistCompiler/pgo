package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class TwoPhaseCommitNoTypeAnnotationParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		return v;
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommitNoTypeAnnotation";
	}

	@Override
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + "TwoPhaseCommit");
		return IOUtils.toString(inputStream);
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
