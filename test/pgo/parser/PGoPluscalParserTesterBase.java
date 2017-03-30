package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.PGoPluscalTesterBase;
import pgo.trans.intermediate.model.PGoAnnotation;

/**
 * Abstract class for testing parsing of real pluscal algorithms. This class
 * will store the data of the expected parsed result to test them.
 *
 */
public abstract class PGoPluscalParserTesterBase extends PGoPluscalTesterBase {

	/**
	 * Gets the expected lines of annotation to be parsed
	 * 
	 * @return
	 */
	public abstract Vector<PGoAnnotation> getAnnotations();

	/**
	 * Gets the expected AST as a string
	 * 
	 * @return
	 * @throws IOException
	 */
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + getAlg());
		return IOUtils.toString(inputStream);
	}

}
