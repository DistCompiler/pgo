package pgo.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.intermediate.PGoContainerType;
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
		v.add(new PGoAnnotation("const uint64 MAXINT 10000000", 8));
		v.add(new PGoAnnotation("arg uint64 RUNS runs", 9));
		v.add(new PGoAnnotation("arg uint64 N numT", 9));
		v.add(new PGoAnnotation("var []chan[[2]interface] network", 13));
		v.add(new PGoAnnotation("func SendTo() uint64 uint64 interface", 16));
		v.add(new PGoAnnotation("func Recv() uint64 uint64 interface", 21));
		v.add(new PGoAnnotation("proc uint64 Client", 29));
		v.add(new PGoAnnotation("var uint64 a_init", 31));
		v.add(new PGoAnnotation("var uint64 b_init", 32));
		v.add(new PGoAnnotation("var uint64 runs", 33));
		v.add(new PGoAnnotation("var uint64 Client.id", 34));
		v.add(new PGoAnnotation("var uint64 Client.msg", 35));
		v.add(new PGoAnnotation("var uint64 sum", 36));
		v.add(new PGoAnnotation("proc uint64 Server", 58));
		v.add(new PGoAnnotation("var uint64 a", 60));
		v.add(new PGoAnnotation("var uint64 b", 61));
		v.add(new PGoAnnotation("var uint64 Server.id", 62));
		v.add(new PGoAnnotation("var [2]uint64 Server.msg", 63));
		return v;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<VarAnnotatedVariableData>();
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSlice("chan[[2]interface]"), "network", 13));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "a_init", 31));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "b_init", 32));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "runs", 33));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Client.id", 34));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Client.msg", 35));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "sum", 36));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "a", 60));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "b", 61));
		ret.add(new VarAnnotatedVariableData(new PGoPrimitiveType.PGoNatural(), "Server.id", 62));
		ret.add(new VarAnnotatedVariableData(new PGoContainerType.PGoSlice("2", "interface"), "Server.msg", 63));

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
		ArrayList<AnnotatedProcessData> ret = new ArrayList<AnnotatedProcessData>();
		ret.add(new AnnotatedProcessData("Client", 29, new PGoPrimitiveType.PGoNatural()));
		ret.add(new AnnotatedProcessData("Server", 58, new PGoPrimitiveType.PGoNatural()));

		return ret;
	}

	@Override
	protected String getAlg() {
		return "Sum";
	}

}
