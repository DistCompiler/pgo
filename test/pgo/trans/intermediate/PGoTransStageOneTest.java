package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.json.JSONObject;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.PGoPluscalStageTesterBase.TestFunctionData;
import pgo.trans.intermediate.PGoPluscalStageTesterBase.TestVariableData;

@RunWith(Parameterized.class)
public class PGoTransStageOneTest {

	protected PGoPluscalStageTesterBase tester;

	public PGoTransStageOneTest(PGoPluscalStageTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { new EuclidIntermediateTester() },
				{ new QueensPluscalIntermediateTester() }, { new SumIntermediateTester() },
				{ new TwoPhaseCommitIntermediateTester() } });
	}

	@Test
	public void testUniOrMultiProcess() throws PGoTransException, PGoParseException, PGoOptionException {

		PGoTransStageInitParse p = new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()));
		assertEquals(tester.isMultiProcess(), p.data.isMultiProcess);
	}

	@Test
	public void testAlgName() throws PGoTransException, PGoParseException, PGoOptionException {
		PGoTransStageInitParse p = new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()));
		assertEquals(tester.getName(), p.data.algName);

	}

	@Test
	public void testPGoVariable() throws PGoTransException, PGoParseException, PGoOptionException {
		PGoTransStageInitParse p = new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()));
		ArrayList<PGoVariable> cv = new ArrayList<>(p.data.globals.values());
		assertEquals(tester.getStageOneVariables().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoVariable(cv.get(i), i, tester.getStageOneVariables());
			assertEquals(cv.get(i), p.data.globals.get(cv.get(i).getName()));
		}
	}

	// assert function for a pgovariable generated from initial pass
	private void assertPGoVariable(PGoVariable v, int i, ArrayList<TestVariableData> tv) {
		TestVariableData av = tv.get(i);

		assertNotNull(v);
		assertEquals(av.name, v.getName());
		assertEquals(av.isSimpleInit, v.getIsSimpleAssignInit());
		assertEquals(av.initBlock, v.getPcalInitBlock().toString());
	}

	@Test
	public void testPGoFunction() throws PGoTransException, PGoParseException, PGoOptionException {
		PGoTransStageInitParse p = new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()));

		ArrayList<PGoFunction> cv = new ArrayList<>(p.data.funcs.values());
		assertEquals(tester.getStageOneFunctions().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoFunction(p, i, tester);
		}
	}

	// assert function for a pgofunction generated from initial pass
	private void assertPGoFunction(PGoTransStageInitParse p, int i, PGoPluscalStageTesterBase tester)
			throws PGoParseException {
		TestFunctionData af = tester.getStageOneFunctions().get(i);

		ArrayList<PGoFunction> funcs = new ArrayList<>(p.data.funcs.values());
		PGoFunction f = funcs.get(i);
		assertNotNull(f);
		assertEquals(af.name, f.getName());
		assertEquals(af.body, f.getBody().toString());

		assertEquals(af.params.size(), f.getParams().size());
		for (int j = 0; j < f.getParams().size(); j++) {
			assertPGoVariable(f.getParams().get(j), j, af.params);
			assertEquals(f.getParams().get(j), f.getParam(f.getParams().get(j).getName()));
		}

		assertEquals(af.vars.size(), f.getVariables().size());
		for (int j = 0; j < f.getVariables().size(); j++) {
			assertPGoVariable(f.getVariables().get(j), j, af.vars);
			assertEquals(f.getVariables().get(j), f.getVariable(f.getVariables().get(j).getName()));
		}

		assertEquals(p.data.funcs.get(af.name), f);

		assertEquals(af.type, f.getType());
	}

	@Test
	public void assertGoRoutineInit() throws PGoTransException, PGoParseException, PGoOptionException {
		PGoTransStageInitParse p = new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()));

		ArrayList<PGoRoutineInit> grs = new ArrayList<>(p.data.goroutines.values());
		assertEquals(tester.getNumGoroutineInit(), grs.size());

		for (TestFunctionData f : tester.getStageOneFunctions()) {
			if (f.type == PGoFunction.FunctionType.GoRoutine) {
				PGoRoutineInit gr = p.data.goroutines.get(f.name);
				assertNotNull(gr);
				assertEquals(f.name, gr.getName());
				assertEquals(f.isGoSimpleInit, gr.getIsSimpleInit());
				assertEquals(f.goroutineInit, gr.getInitTLA().toString());
			}
		}
	}
}
