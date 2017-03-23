package pgo.pcalparser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the variables, functions and other data of the pluscal
 * algorithm to be used for validating the parsed and translated version of the
 * algorithm with the actual data.
 *
 */
public class EuclidNoAnnotationPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<String> getAnnotations() {
		return new Vector<String>();
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

}
