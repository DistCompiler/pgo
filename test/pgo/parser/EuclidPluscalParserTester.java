package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the Euclid pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class EuclidPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg int N", 6));
		v.add(new PGoAnnotation("var int u", 7));
		return v;
	}

	@Override
	protected String getAlg() {
		return "Euclid";
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<ArgAnnotatedVariableData>();
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "N", 6, true, ""));

		return ret;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "u", 7));
		return ret;
	}

	@Override
	public int getNumberAnnotatedVariables() {
		return 2;
	}

}
