package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;
import pgo.trans.intermediate.PGoPluscalStageTesterBase.TestFunctionData;
import pgo.trans.intermediate.PGoPluscalStageTesterBase.TestVariableData;

// Test the result of atomicity inference stage
@RunWith(Parameterized.class)
public class PGoTransStageAtomicityTest {

	protected PGoPluscalStageTesterBase tester;
	private PGoTransStageAtomicity p;

	public PGoTransStageAtomicityTest(PGoPluscalStageTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { new EuclidIntermediateTester() }, { new FastMutexIntermediateTester() },
				{ new QueensPluscalIntermediateTester() }, { new QueensPluscalProcedureIntermediateTester() },
				{ new SumIntermediateTester() }, { new TwoPhaseCommitIntermediateTester() } });
	}

	@Before
	public void SetUp() throws PGoParseException, PGoTransException {
		PGoTransStageOne.init(tester.getParsedPcal());
		PGoTransStageType.init(PGoTransStageOne.instance);
		PGoTransStageAtomicity.init(PGoTransStageType.instance);
		p = PGoTransStageAtomicity.instance;
	}

	@Test
	public void testUniOrMultiProcess() throws PGoTransException, PGoParseException {
		assertEquals(tester.isMultiProcess(), p.getIsMultiProcess());
	}

	@Test
	public void testAlgName() throws PGoTransException, PGoParseException {
		assertEquals(tester.getName(), p.getAlgName());
	}

	@Test
	public void testPGoVariable() throws PGoTransException, PGoParseException {
		ArrayList<PGoVariable> cv = p.getGlobals();
		assertEquals(tester.getStageTypeVariables().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoVariable(p.getGlobals().get(i), i, tester.getStageTypeVariables());
			assertEquals(p.getGlobals().get(i), p.getGlobal(p.getGlobals().get(i).getName()));
		}
	}

	// assert function for a pgovariable generated from initial pass
	private void assertPGoVariable(PGoVariable v, int i, ArrayList<TestVariableData> tv) {
		TestVariableData av = tv.get(i);

		assertNotNull(v);
		assertEquals(av.name, v.getName());
		assertEquals(av.isSimpleInit, v.getIsSimpleAssignInit());
		assertEquals(av.initBlock, v.getPcalInitBlock().toString());

		assertEquals(av.atomicity, v.getIsAtomic());
		assertEquals(av.goVal, v.getGoVal());
		assertEquals(av.isConst, v.getIsConstant());
		assertEquals(av.type, v.getType());
		if (av.isPositionalArg || !av.argFlag.isEmpty()) {
			assertNotNull(v.getArgInfo());
			assertEquals(av.isPositionalArg, v.getArgInfo().isPositionalArg());
			assertEquals(av.argFlag, v.getArgInfo().getArgName());
		} else {
			assertNull(v.getArgInfo());
		}
	}

	@Test
	public void testPGoFunction() throws PGoTransException, PGoParseException {
		ArrayList<PGoFunction> cv = p.getFunctions();
		assertEquals(tester.getStageTypeFunctions().size(), cv.size());

		for (int i = 0; i < cv.size(); i++) {
			assertPGoFunction(p, i, tester);
		}
	}

	// assert function for a pgofunction generated from initial pass
	private void assertPGoFunction(PGoTransStageAtomicity p2, int i, PGoPluscalStageTesterBase tester)
			throws PGoParseException {
		TestFunctionData af = tester.getStageTypeFunctions().get(i);

		PGoFunction f = p2.getFunctions().get(i);
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

		assertEquals(p2.getFunction(af.name), f);
		
		assertEquals(af.type, f.getType());

		assertEquals(af.retType, f.getReturnType());
	}

	@Test
	public void assertGoRoutineInit() throws PGoTransException, PGoParseException {
		PGoTransStageOne.init(tester.getParsedPcal());
		PGoTransStageOne p = PGoTransStageOne.instance;

		ArrayList<PGoRoutineInit> grs = p.getGoRoutineInits();
		assertEquals(tester.getNumGoroutineInit(), grs.size());
		
		for (TestFunctionData f : tester.getStageOneFunctions()) {
			if (f.type == PGoFunction.FunctionType.GoRoutine) {
				PGoRoutineInit gr = p.getGoRoutineInit(f.name);
				assertNotNull(gr);
				assertEquals(f.name, gr.getName());
				assertEquals(f.isGoSimpleInit, gr.getIsSimpleInit());
				assertEquals(f.goroutineInit, gr.getInitTLA().toString());
			}
		}
	}
}
