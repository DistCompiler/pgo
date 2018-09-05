package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.mpcal;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.mpcal.ModularPlusCalBlock;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

@RunWith(Parameterized.class)
public class ModularPlusCalParserTest {
	@Parameterized.Parameters
	public static List<Object[]> data() {
		return Arrays.asList(new Object[][] {
				{"---- MODULE Test ----\n" +
						"(* --mpcal Test {\n" +
						"}\n" +
						"*)",
						mpcal("Test", Collections.emptyList(), Collections.emptyList())
				},
		});
	}

	private String blockString;
	private ModularPlusCalBlock blockExpected;

	public ModularPlusCalParserTest(String blockString, ModularPlusCalBlock blockExpected) {
		this.blockString = blockString;
		this.blockExpected = blockExpected;
	}

	private static final Path testFile = Paths.get("TEST");

	@Test
	public void test() throws ParseFailureException {
		LexicalContext ctx = new LexicalContext(
				testFile,
				String.join(System.lineSeparator(), blockString.split("\n")));
		System.out.println(blockString);
		ModularPlusCalBlock block = ModularPlusCalParser.readBlock(ctx);
		assertThat(block, is(blockExpected));
	}
}
