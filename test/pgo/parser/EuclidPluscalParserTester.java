package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;
import pgo.model.type.PGoTypeInt;

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
		Vector<PGoAnnotation> v = new Vector<>();
		v.add(new PGoAnnotation("arg N int", 6));
		v.add(new PGoAnnotation("var u int", 7));
		v.add(new PGoAnnotation("var v int", 8));
		v.add(new PGoAnnotation("var v_init int", 9));
		return v;
	}

	@Override
	protected String getAlg() {
		return "Euclid";
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<>();
		ret.add(new ArgAnnotatedVariableData(PGoTypeInt.getInstance(), "N", 6, true, ""));

		return ret;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<>();
		ret.add(new VarAnnotatedVariableData(PGoTypeInt.getInstance(), "u", 7));
		ret.add(new VarAnnotatedVariableData(PGoTypeInt.getInstance(), "v", 8));
		ret.add(new VarAnnotatedVariableData(PGoTypeInt.getInstance(), "v_init", 9));
		return ret;
	}

}
