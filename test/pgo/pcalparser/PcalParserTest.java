package pgo.pcalparser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.pcalparser.PcalParser.ParsedPcal;

@RunWith(Parameterized.class)
public class PcalParserTest {

	protected PGoPluscalParserTesterBase tester;

	public PcalParserTest(PGoPluscalParserTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { new EuclidPluscalParserTester() },
				{ new EuclidNoAnnotationPluscalParserTester() } });
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
			assertTrue(tester.getASTString().contains(pa.getAST().toString()));
		} catch (PcalParseException e) {
			if (!tester.expectException()) {
				fail("Unexpected PcalParseException: " + e.getMessage());
			}
		}

	}
}
