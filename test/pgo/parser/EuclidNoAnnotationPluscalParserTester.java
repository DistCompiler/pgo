package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 */
public class EuclidNoAnnotationPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		return new Vector<PGoAnnotation>();
	}

	@Override
	public boolean expectException() {
		return false;
	}

	@Override
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + "Euclid");
		return IOUtils.toString(inputStream);
	}

	@Override
	protected String getAlg() {
		return "EuclidNoAnnotation";
	}

	@Override
	public int exceptionLine() {
		return 0;
	}

}
