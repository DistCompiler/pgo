package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Vector;

import pcal.AST.LabeledStmt;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;

/**
 * Base abstract class for all stages to manage the data
 *
 */
public abstract class PGoTransStageBase {

	// The intermediate data
	PGoTransIntermediateData intermediateData;

	public PGoTransStageBase() {
		this.intermediateData = new PGoTransIntermediateData();
	}

	public PGoTransStageBase(PGoTransStageBase s) {
		this.intermediateData = s.intermediateData;
	}

	public boolean getIsMultiProcess() {
		return intermediateData.isMultiProcess;
	}

	public String getAlgName() {
		return intermediateData.algName;
	}

	public ArrayList<PGoVariable> getGlobals() {
		return new ArrayList<PGoVariable>(intermediateData.globals.values());
	}

	public PGoVariable getGlobal(String name) {
		return intermediateData.globals.get(name);
	}

	public ArrayList<PGoFunction> getFunctions() {
		return new ArrayList<PGoFunction>(intermediateData.funcs.values());
	}

	public PGoFunction getFunction(String name) {
		return intermediateData.funcs.get(name);
	}

	public Vector<LabeledStmt> getMain() {
		return intermediateData.mainBlock;
	}

	public ArrayList<PGoRoutineInit> getGoRoutineInits() {
		return new ArrayList<PGoRoutineInit>(intermediateData.goroutines.values());
	}

	public PGoRoutineInit getGoRoutineInit(String r) {
		return intermediateData.goroutines.get(r);
	}
}
