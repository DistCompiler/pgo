package pgo.parser;

import pgo.model.parser.PGoAnnotation;
import pgo.model.type.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

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
		Vector<PGoAnnotation> v = new Vector<>();
		v.add(new PGoAnnotation("const MAXINT uint64 10000000", 8));
		v.add(new PGoAnnotation("arg RUNS uint64 runs", 9));
		v.add(new PGoAnnotation("arg N uint64 numT", 9));
		v.add(new PGoAnnotation("var network []chan[[]interface{}]", 13));
		v.add(new PGoAnnotation("func SendTo() uint64 uint64 interface{}", 16));
		v.add(new PGoAnnotation("func Recv() uint64 uint64 interface{}", 21));
		v.add(new PGoAnnotation("var a_init uint64", 30));
		v.add(new PGoAnnotation("var b_init uint64", 31));
		v.add(new PGoAnnotation("var runs uint64", 32));
		v.add(new PGoAnnotation("var Client.id uint64", 33));
		v.add(new PGoAnnotation("var Client.msg uint64", 34));
		v.add(new PGoAnnotation("var sum uint64", 35));
		v.add(new PGoAnnotation("var a uint64", 58));
		v.add(new PGoAnnotation("var b uint64", 59));
		v.add(new PGoAnnotation("var Server.id uint64", 60));
		v.add(new PGoAnnotation("var Server.msg []uint64", 61));
		return v;
	}

	@Override
	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		ArrayList<VarAnnotatedVariableData> ret = new ArrayList<>();
		ret.add(new VarAnnotatedVariableData(new PGoTypeSlice(new PGoTypeChan(new PGoTypeSlice(PGoTypeInterface.getInstance()))), "network", 13));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "a_init", 30));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "b_init", 31));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "runs", 32));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "Client.id", 33));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "Client.msg", 34));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "sum", 35));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "a", 58));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "b", 59));
		ret.add(new VarAnnotatedVariableData(PGoTypeNatural.getInstance(), "Server.id", 60));
		ret.add(new VarAnnotatedVariableData(new PGoTypeSlice(PGoTypeNatural.getInstance()), "Server.msg", 61));

		return ret;
	}

	@Override
	public List<ConstAnnotatedVariableData> getConstAnnotatedVariables() {
		ArrayList<ConstAnnotatedVariableData> ret = new ArrayList<>();
		ret.add(new ConstAnnotatedVariableData(PGoTypeNatural.getInstance(), "MAXINT", 8, "10000000"));

		return ret;
	}

	@Override
	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		ArrayList<ArgAnnotatedVariableData> ret = new ArrayList<>();
		ret.add(new ArgAnnotatedVariableData(PGoTypeNatural.getInstance(), "RUNS", 9, false, "runs"));
		ret.add(new ArgAnnotatedVariableData(PGoTypeNatural.getInstance(), "N", 9, false, "numT"));

		return ret;
	}

	@Override
	public List<AnnotatedFunctionData> getAnnotatedFunctions() {
		ArrayList<AnnotatedFunctionData> ret = new ArrayList<>();
		Vector<PGoType> args = new Vector<>();
		args.add(PGoTypeNatural.getInstance());
		args.add(PGoTypeNatural.getInstance());
		args.add(PGoTypeInterface.getInstance());
		ret.add(new AnnotatedFunctionData("SendTo", 16, PGoTypeVoid.getInstance(), args));
		ret.add(new AnnotatedFunctionData("Recv", 21, PGoTypeVoid.getInstance(), args));

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
