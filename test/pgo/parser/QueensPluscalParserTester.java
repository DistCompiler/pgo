package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
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
		v.add(new PGoAnnotation("var Set[[]int] todo", 46));
		v.add(new PGoAnnotation("var Set[[]int] sols", 47));
		v.add(new PGoAnnotation("macro Attacks(queens []int,i int,j int) ==\n"
				+ "                \\/ queens[i] = queens[j]                 \\** same column\n"
				+ "                \\/ queens[i] - queens[j] = i - j         \\** first diagonal\n"
				+ "                \\/ queens[j] - queens[i] = i - j         \\** second diagonal", 51));
		v.add(new PGoAnnotation("macro IsSolution(queens []int) ==\n"
				+ "                \\A i \\in 1 .. Len(queens)-1 : \\A j \\in i+1 .. Len(queens) : \n"
				+ "                ~ Attacks(queens,i,j)", 54));
		v.add(new PGoAnnotation("var []int queens", 62));
		v.add(new PGoAnnotation("var int nxtQ", 63));
		v.add(new PGoAnnotation("var Set[int] cols", 64));
		v.add(new PGoAnnotation("var Set[[]int] exts", 65));
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
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("[]int"), "todo", 46));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("[]int"), "sols", 47));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSlice("int"), "queens", 62));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "nxtQ", 63));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("int"), "cols", 64));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("[]int"), "exts", 65));

		return ret;
	}

}
