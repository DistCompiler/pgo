package pgo.parser;

import java.util.Vector;

import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the TwoPhaseCommit pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class TwoPhaseCommitParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("func void SetAll() string map[string]string", 9));
		return v;
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommit";
	}

}
