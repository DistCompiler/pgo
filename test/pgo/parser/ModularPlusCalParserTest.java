package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.mpcal.ModularPlusCalUnit;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

@RunWith(Parameterized.class)
public class ModularPlusCalParserTest {
	@Parameterized.Parameters
	public static List<Object[]> data() {
		return Arrays.asList();
	}

	private static final Path testFile = Paths.get("TEST");

	private String unitString;
	private ModularPlusCalUnit unitExpected;

	public ModularPlusCalParserTest(String unitString, ModularPlusCalUnit unitExpected) {
		this.unitString = unitString;
		this.unitExpected = unitExpected;
	}

	@Test
	public void test() {
		LexicalContext ctx = new LexicalContext(testFile, String.join(System.lineSeparator(), unitString.split("\n")));
		System.out.println(unitString);
		ModularPlusCalUnit unit = ModularPlusCalParser.readUnit(ctx);
		assertThat(unit, is(unitExpected));
	}
}
