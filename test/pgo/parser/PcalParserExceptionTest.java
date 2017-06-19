package pgo.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.PGoPluscalTesterBase;

// Tests that exceptions should be thrown.
@RunWith(Parameterized.class)
public class PcalParserExceptionTest extends PGoPluscalTesterBase {

	// The algorithm name
	private String alg;

	// The expected line in pluscal that cased the exception
	private int line;

	public PcalParserExceptionTest(String alg, int line) {
		this.alg = "annotationtests/" + alg;
		this.line = line;
	}

	@Parameterized.Parameters
	public static Collection primeNumbers() {
		return Arrays.asList(new Object[][] { { "AnnotationNoEndNewLineCommentLine", 6 },
				{ "AnnotationNoEndNewLineCommentBlock", 14 }, { "AnnotationNoEndBlockCommentEnd", 7 },
				{ "AnnotationNoEndTokenWrong1", 15 }, { "AnnotationNoEndTokenWrong2", 11 },
				{ "AnnotationNoEndTokenWrong3", 8 }, { "AnnotationNoEndTokenWrong4", 7 },
				{ "AnnotationNoEndTokenWrong5", 6 }, { "AnnotationUnexpectedBeginToken", 18 },
				{ "AnnotationUnexpectedEndToken", 18}, { "No such file", -1 }
			});
	}

	@Test
	public void test() {
		try {
			getParsedPcal();
			fail("Expected PGoParseException");
		} catch (PGoParseException e) {
			assertEquals(line, e.getLine());
		}
	}

	@Override
	protected String getAlg() {
		return alg;
	}

}
