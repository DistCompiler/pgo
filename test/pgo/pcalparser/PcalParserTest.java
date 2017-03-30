package pgo.pcalparser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import static org.junit.matchers.JUnitMatchers.containsString;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;
import pgo.parser.PcalParser.ParsedPcal;

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
	public void testParse() throws IOException {
		PcalParser p = new PcalParser(tester.getPcalPath());
		try {
			ParsedPcal pa = p.parse();
			if (tester.expectException()) {
				fail("Expected PcalParseException");
			}
			assertEquals(tester.getAnnotations(), pa.getPGoAnnotations());
			Assert.assertThat(tester.getASTString(), containsString(pa.getAST().toString()));
		} catch (PGoParseException e) {
			if (!tester.expectException()) {
				fail("Unexpected PcalParseException: " + e.getMessage());
			}
		}

	}
}
