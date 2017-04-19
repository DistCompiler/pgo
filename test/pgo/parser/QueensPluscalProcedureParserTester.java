package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the Queens pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class QueensPluscalProcedureParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg int N", 45));
		v.add(new PGoAnnotation("ret rVal", 49));
		return v;
	}

	@Override
	protected String getAlg() {
		return "QueensPluscalProcedure";
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<ArgAnnotatedVariableData>();
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "N", 45, true, ""));

		return ret;
	}

	@Override
	public int getNumberAnnotatedVariables() {
		return 1;
	}
}
