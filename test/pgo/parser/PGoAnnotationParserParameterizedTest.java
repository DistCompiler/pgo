package pgo.parser;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.parser.AnnotatedFunction;
import pgo.model.parser.AnnotatedProcess;
import pgo.model.parser.AnnotatedReturnVariable;
import pgo.model.parser.AnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.ConstAnnotatedVariable;
import pgo.model.parser.AnnotatedVariable.VarAnnotatedVariable;
import pgo.model.type.PGoTypeGenerator;
import pgo.parser.PGoPluscalParserTesterBase.*;
import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.PGoTransException;

import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.*;

// Parameterized annotation parser test class that checks each pluscal file
@RunWith(Parameterized.class)
public class PGoAnnotationParserParameterizedTest {

	protected PGoPluscalParserTesterBase tester;
	protected PGoTypeGenerator generator;

	public PGoAnnotationParserParameterizedTest(PGoPluscalParserTesterBase tester) {
		this.tester = tester;
		this.generator = new PGoTypeGenerator("test");
	}

	@Parameterized.Parameters
	public static Collection testSpecifications() {
		return Arrays
				.asList(new Object[][] { { new EuclidPluscalParserTester() },
						{ new QueensPluscalParserTester() }, { new SumParserTester() },
						{ new TwoPhaseCommitParserTester() },
				 });
	}

	@Test
	public void testParse() throws PGoParseException, PGoTransException {
		PcalParser p = new PcalParser(tester.getPcalPath());

		ParsedPcal pp = p.parse();
		PGoAnnotationParser pa = new PGoAnnotationParser(pp.getPGoAnnotations(), generator);

		assertEquals(tester.getNumberAnnotatedVariables(), pa.getAnnotatedVariables().size());
		for (ConstAnnotatedVariableData tv : tester.getConstAnnotatedVariables()) {
			AnnotatedVariable v = pa.getAnnotatedVariable(tv.name);
			assertNotNull(v);
			assertTrue(v instanceof ConstAnnotatedVariable);
			assertEquals(tv.name, v.getName());
			assertEquals(tv.type, v.getType());
			assertEquals(tv.line, v.getLine());
			
			ConstAnnotatedVariable cv = (ConstAnnotatedVariable) v;
			assertEquals(tv.val, cv.getVal());
		}

		for (ArgAnnotatedVariableData tv : tester.getArgAnnotatedVariables()) {
			AnnotatedVariable v = pa.getAnnotatedVariable(tv.name);
			assertNotNull(v);
			assertTrue(v instanceof ArgAnnotatedVariable);
			assertEquals(tv.name, v.getName());
			assertEquals(tv.type, v.getType());
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
			assertEquals(tv.type, v.getType());
			assertEquals(tv.line, v.getLine());
		}
		
		assertEquals(tester.getNumberAnnotatedFunctions(), pa.getAnnotatedFunctions().size());
		for (AnnotatedFunctionData tf : tester.getAnnotatedFunctions()) {
			AnnotatedFunction f = pa.getAnnotatedFunction(tf.name);
			assertNotNull(f);
			assertEquals(tf.name, f.getName());
			assertEquals(tf.line, f.getLine());
			assertEquals(tf.rType, f.getReturnType());
			assertEquals(tf.argTypes.size(), f.getArgTypes().size());
			for (int i = 0; i < tf.argTypes.size(); i++) {
				assertEquals(tf.argTypes.get(i), f.getArgTypes().get(i));
			}
		}
		
		assertEquals(tester.getNumberReturnVariables(), pa.getReturnVariables().size());
		for (ReturnVariableData tr : tester.getReturnVariables()) {
			AnnotatedReturnVariable r = pa.getReturnVariable(tr.name);
			assertNotNull(r);
			assertEquals(tr.name, r.getName());
			assertEquals(tr.line, r.getLine());
		}
		
		assertEquals(tester.getNumberAnnotatedProcesses(), pa.getAnnotatedProcesses().size());
		for (AnnotatedProcessData tp : tester.getAnnotatedProcesses()) {
			AnnotatedProcess ap = pa.getAnnotatedProcess(tp.name);
			assertNotNull(ap);
			assertEquals(tp.name, ap.getName());
			assertEquals(tp.line, ap.getLine());
			assertEquals(tp.idType.getClass(), ap.getIdType().getClass());
		}
	}
}
