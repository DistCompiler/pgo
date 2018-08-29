package pgo;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.*;

import static pgo.IntegrationTestingUtils.testCompileFile;
import static pgo.IntegrationTestingUtils.testRunGoCode;

@RunWith(Parameterized.class)
public class TestCodeGenRunTest {
	private String fileName;
	private Map<String, String> constants;
	private List<String> expected;

	public TestCodeGenRunTest(String fileName, Map<String, String> constants, List<String> expected) {
		this.fileName = fileName;
		this.constants = constants;
		this.expected = expected;
	}

	@Parameterized.Parameters
	public static List<Object[]> data() {
		return Arrays.asList(new Object[][] {
				{
						"SimpleEither.tla",
						Collections.emptyMap(),
						Arrays.asList("[1 30]", "[1 30]", "[1 30]"),
				},
				{
						"EitherBothBranches.tla",
						Collections.emptyMap(),
						Arrays.asList("[10 20]", "[10 20]"),
				},
				{
						"EitherRepeatedExec.tla",
						Collections.emptyMap(),
						Collections.singletonList("3"),
				},
				{
					"Procedures.tla",
					new HashMap<String, String>() {
						{
							put("N", "20");
							put("defaultInitValue", "0");
						}
					},
					Arrays.asList("1", "2", "fizz", "4", "buzz", "fizz", "7", "8", "fizz", "buzz",
							"11", "fizz", "13", "14", "fizzbuzz", "16", "17", "fizz", "19", "buzz"),
				}
		});
	}

	@Test
	public void test() throws IOException {
		testCompileFile(Paths.get("test", "integration", fileName), constants,
				compiledFilePath -> testRunGoCode(compiledFilePath, expected));
	}
}
