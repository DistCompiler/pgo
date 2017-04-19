package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the Sum pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class SumParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("const uint64 MAXINT 10000000", 8));
		v.add(new PGoAnnotation("arg uint64 RUNS runs", 9));
		v.add(new PGoAnnotation("arg uint64 N numT", 9));
		v.add(new PGoAnnotation("func SendTo() uint64 uint64 []chan[string]", 15));
		return v;
	}

	@Override
	public List<ConstAnnotatedVariableData> getConstAnnotatedVariables() {
		ArrayList<ConstAnnotatedVariableData> ret = new ArrayList<ConstAnnotatedVariableData>();
		ret.add(new ConstAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "MAXINT", 8, "10000000"));

		return ret;
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<ArgAnnotatedVariableData>();
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "RUNS", 9, false, "runs"));
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "N", 9, false, "numT"));

		return ret;
	}

	@Override
	public int getNumberAnnotatedVariables() {
		return 3;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

}
