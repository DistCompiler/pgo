package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoContainerType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the Queens pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class QueensPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg int N", 45));
		v.add(new PGoAnnotation("var Set[chan[int]] todo", 46));
		v.add(new PGoAnnotation("var Set[chan[int]] sols", 47));
		v.add(new PGoAnnotation("var chan[int] queens", 55));
		v.add(new PGoAnnotation("var int nexQ", 56));
		v.add(new PGoAnnotation("var Set[int] cols", 57));
		v.add(new PGoAnnotation("var Set[chan[int]] exts", 58));
		return v;
	}

	@Override
	protected String getAlg() {
		return "QueensPluscal";
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<ArgAnnotatedVariableData>();
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "N", 45, true, ""));

		return ret;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSet("chan[int]"), "todo", 46));
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSet("chan[int]"), "sols", 47));
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoChan("int"), "queens", 55));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "nexQ", 56));
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSet("int"), "cols", 57));
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSet("chan[int]"), "exts", 58));

		return ret;
	}

}
