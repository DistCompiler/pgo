package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.matchers.JUnitMatchers.containsString;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.parser.PcalParser.ParsedPcal;
import pgo.trans.intermediate.model.PGoAnnotation;

@RunWith(Parameterized.class)
public class PcalParserTest {

	protected PGoPluscalParserTesterBase tester;

	public PcalParserTest(PGoPluscalParserTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { new AnnotationTestParserTester() }, { new EuclidPluscalParserTester() },
				{ new EuclidNoAnnotationPluscalParserTester() }, { new FastMutexPluscalParserTester() },
				{ new FastMutexNoAnnotationPluscalParserTester() }, { new QueensPluscalParserTester() },
				{ new QueensPluscalProcedureParserTester() }, { new SumParserTester() },
				{ new SumNoTypeAnnotationParserTester() }, { new TwoPhaseCommitParserTester() },
				{ new TwoPhaseCommitNoTypeAnnotationParserTester() } });
	}

	@Test
	public void testParse() throws IOException, PGoParseException {
		PcalParser p = new PcalParser(tester.getPcalPath());

		ParsedPcal pa = p.parse();

		assertEquals(tester.getAnnotations().size(), pa.getPGoAnnotations().size());
		for (int i = 0; i < tester.getAnnotations().size(); i++) {
			PGoAnnotation exp = tester.getAnnotations().get(i);
			PGoAnnotation act = pa.getPGoAnnotations().get(i);
			assertEquals(exp.getString(), act.getString());
			assertEquals(exp.getLine(), act.getLine());
		}

		Assert.assertThat(tester.getASTString(), containsString(pa.getAST().toString()));

	}
}
