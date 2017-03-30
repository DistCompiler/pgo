package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for parsing the FastMutex pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class FastMutexNoAnnotationPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		return new Vector<PGoAnnotation>();
	}

	@Override
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + "FastMutex");
		return IOUtils.toString(inputStream);
	}

	@Override
	protected String getAlg() {
		return "FastMutexNoAnnotation";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
