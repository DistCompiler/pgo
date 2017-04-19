package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ConstAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.parser.PGoPluscalParserTesterBase.ArgAnnotatedVariableData;
import pgo.parser.PGoPluscalParserTesterBase.ConstAnnotatedVariableData;
import pgo.parser.PGoPluscalParserTesterBase.VarAnnotatedVariableData;
import pgo.parser.PcalParser.ParsedPcal;

// Parameterized annotation parser test class that checks each pluscal file
@RunWith(Parameterized.class)
public class PGoAnnotationParserParameterizedTest {

	protected PGoPluscalParserTesterBase tester;

	public PGoAnnotationParserParameterizedTest(PGoPluscalParserTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays
				.asList(new Object[][] { { new EuclidPluscalParserTester() },
						{ new FastMutexPluscalParserTester() }, { new QueensPluscalParserTester() },
						{ new QueensPluscalProcedureParserTester() }, { new SumParserTester() },
						{ new TwoPhaseCommitParserTester() },
				 });
	}

	@Test
	public void testParse() throws IOException, PGoParseException {
		PcalParser p = new PcalParser(tester.getPcalPath());

		ParsedPcal pp = p.parse();
		PGoAnnotationParser pa = new PGoAnnotationParser(pp.getPGoAnnotations());

		assertEquals(tester.getNumberAnnotatedVariables(), pa.getAnnotatedVariables().size());
		for (ConstAnnotatedVariableData tv : tester.getConstAnnotatedVariables()) {
			AnnotatedVariable v = pa.getAnnotatedVariable(tv.name);
			assertNotNull(v);
			assertTrue(v instanceof ConstAnnotatedVariable);
			assertEquals(tv.name, v.getName());
			assertEquals(tv.type.getClass(), v.getType().getClass());
			assertEquals(tv.line, v.getLine());
			
			ConstAnnotatedVariable cv = (ConstAnnotatedVariable) v;
			assertEquals(tv.val, cv.getVal());
		}

		for (ArgAnnotatedVariableData tv : tester.getArgAnnotatedVariables()) {
			AnnotatedVariable v = pa.getAnnotatedVariable(tv.name);
			assertNotNull(v);
			assertTrue(v instanceof ArgAnnotatedVariable);
			assertEquals(tv.name, v.getName());
			assertEquals(tv.type.getClass(), v.getType().getClass());
			assertEquals(tv.line, v.getLine());

			ArgAnnotatedVariable av = (ArgAnnotatedVariable) v;
			assertEquals(tv.isPositional, av.isPositionalArg());
			assertEquals(tv.argName, av.getArgName());
		}

		for (VarAnnotatedVariableData tv : tester.getVarAnnotatedVariables()) {
			AnnotatedVariable v = pa.getAnnotatedVariable(tv.name);
			assertNotNull(v);
			assertTrue(v instanceof VarAnnotatedVariable);
			assertEquals(tv.name, v.getName());
			assertEquals(tv.type.getClass(), v.getType().getClass());
			assertEquals(tv.line, v.getLine());
		}
	}
}
