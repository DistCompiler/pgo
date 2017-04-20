package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.parser.PGoAnnotation;

/**
 * Tester class for the FastMutex pluscal algorithm
 * 
 * This class stores the annotations, exceptions if any, and ast that is
 * expected.
 *
 */
public class FastMutexPluscalParserTester extends PGoPluscalParserTesterBase {

	@Override
	public Vector<PGoAnnotation> getAnnotations() {
		Vector<PGoAnnotation> v = new Vector<PGoAnnotation>();
		v.add(new PGoAnnotation("arg natural N numT", 6));
		v.add(new PGoAnnotation("var natural x", 8));
		v.add(new PGoAnnotation("var natural y", 9));
		v.add(new PGoAnnotation("var []bool b", 10));
		v.add(new PGoAnnotation("proc natural Proc", 11));
		v.add(new PGoAnnotation("var natural j", 12));
		return v;
	}

	@Override
	protected String getAlg() {
		return "FastMutex";
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<ArgAnnotatedVariableData>();
		ret.add(new ArgAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "N", 6, false, "numT"));

		return ret;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "x", 8));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "y", 9));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSlice("bool"), "b", 10));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "j", 12));
		return ret;
	}

	@Override
	public int getNumberAnnotatedVariables() {
		return 5;
	}

	@Override
	public List<AnnotatedProcessData> getAnnotatedProcesses() {
		ArrayList<AnnotatedProcessData> ret = new ArrayList<AnnotatedProcessData>();
		ret.add(new AnnotatedProcessData("Proc", 11, new PGoPrimitiveType.PGoNatural()));
		
		return ret;
	}

}
