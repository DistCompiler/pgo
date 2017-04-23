package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
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
		v.add(new PGoAnnotation("var Set[chan[int]] todo", 46));
		v.add(new PGoAnnotation("var Set[chan[int]] sols", 47));
		v.add(new PGoAnnotation("ret rVal", 51));
		v.add(new PGoAnnotation("func bool Attacks() chan[int] int int", 53));
		v.add(new PGoAnnotation("var chan[int] queens", 64));
		v.add(new PGoAnnotation("var int nexQ", 65));
		v.add(new PGoAnnotation("var Set[int] cols", 66));
		v.add(new PGoAnnotation("var Set[chan[int]] exts", 67));
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
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("chan[int]"), "todo", 46));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("chan[int]"), "sols", 47));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoChan("int"), "queens", 64));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoInt(), "nexQ", 65));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("int"), "cols", 66));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSet("chan[int]"), "exts", 67));

		return ret;
	}

	@Override
	public List<ReturnVariableData> getReturnVariables() {
		ArrayList<ReturnVariableData> ret = new ArrayList<ReturnVariableData>();
		ret.add(new ReturnVariableData("rVal", 51));

		return ret;
	}

	@Override
	public List<AnnotatedFunctionData> getAnnotatedFunctions() {
		ArrayList<AnnotatedFunctionData> ret = new ArrayList<AnnotatedFunctionData>();
		Vector<PGoType> args = new Vector<PGoType>();
		args.add(new PGoCollectionType.PGoChan("int"));
		args.add(new PGoPrimitiveType.PGoInt());
		args.add(new PGoPrimitiveType.PGoInt());
		ret.add(new AnnotatedFunctionData("Attacks", 53, new PGoPrimitiveType.PGoBool(), args));

		return ret;
	}
}
