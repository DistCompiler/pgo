package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
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
		v.add(new PGoAnnotation("var managers Set[String]", 6));
		v.add(new PGoAnnotation("var restaurant_stage map[String]String", 7));
		v.add(new PGoAnnotation("func void SetAll() string Set[string]", 11));
		v.add(new PGoAnnotation("var rstMgrs Set[string]", 42));
		v.add(new PGoAnnotation("var aborted bool", 42));
		return v;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("String"), "managers", 6));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoMap("String", "String"), "restaurant_stage", 7));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("string"), "rstMgrs", 42));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoBool(), "aborted", 42));

		return ret;
	}

	@Override
	public List<AnnotatedFunctionData> getAnnotatedFunctions() {
		ArrayList<AnnotatedFunctionData> ret = new ArrayList<AnnotatedFunctionData>();
		Vector<PGoType> args = new Vector<PGoType>();
		args.add(new PGoPrimitiveType.PGoString());
		args.add(new PGoCollectionType.PGoSet("string"));
		ret.add(new AnnotatedFunctionData("SetAll", 11, PGoType.VOID, args));

		return ret;
	}

	@Override
	public List<AnnotatedProcessData> getAnnotatedProcesses() {
		return new ArrayList<>();
	}

	@Override
	protected String getAlg() {
		return "TwoPhaseCommit";
	}

}
