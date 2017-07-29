package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoCollectionType;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoType;
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
		v.add(new PGoAnnotation("const MAXINT uint64 10000000", 8));
		v.add(new PGoAnnotation("arg RUNS uint64 runs", 9));
		v.add(new PGoAnnotation("arg N uint64 numT", 9));
		v.add(new PGoAnnotation("var network []chan[[2]interface]", 13));
		v.add(new PGoAnnotation("func SendTo() uint64 uint64 interface", 16));
		v.add(new PGoAnnotation("func Recv() uint64 uint64 interface", 21));
		v.add(new PGoAnnotation("var a_init uint64", 30));
		v.add(new PGoAnnotation("var b_init uint64", 31));
		v.add(new PGoAnnotation("var runs uint64", 32));
		v.add(new PGoAnnotation("var Client.id uint64", 33));
		v.add(new PGoAnnotation("var Client.msg uint64", 34));
		v.add(new PGoAnnotation("var sum uint64", 35));
		v.add(new PGoAnnotation("var a uint64", 58));
		v.add(new PGoAnnotation("var b uint64", 59));
		v.add(new PGoAnnotation("var Server.id uint64", 60));
		v.add(new PGoAnnotation("var Server.msg [2]uint64", 61));
		return v;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSlice("chan[[2]interface]"), "network", 13));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "a_init", 30));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "b_init", 31));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "runs", 32));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Client.id", 33));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Client.msg", 34));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "sum", 35));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "a", 58));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "b", 59));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Server.id", 60));
		ret.add(new VarAnnotatedVariableData(new PGoCollectionType.PGoSlice("2", "uint64"), "Server.msg", 61));

		return ret;
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
	public List<AnnotatedFunctionData> getAnnotatedFunctions() {
		ArrayList<AnnotatedFunctionData> ret = new ArrayList<AnnotatedFunctionData>();
		Vector<PGoType> args = new Vector<PGoType>();
		args.add(new PGoPrimitiveType.PGoNatural());
		args.add(new PGoPrimitiveType.PGoNatural());
		args.add(new PGoPrimitiveType.PGoInterface());
		ret.add(new AnnotatedFunctionData("SendTo", 16, PGoType.VOID, args));
		ret.add(new AnnotatedFunctionData("Recv", 21, PGoType.VOID, args));

		return ret;
	}

	@Override
	public List<AnnotatedProcessData> getAnnotatedProcesses() {
		return new ArrayList<>();
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

}
