package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.archetype;
import static pgo.model.pcal.PlusCalBuilder.printS;
import static pgo.model.tla.TLABuilder.num;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.mpcal.ModularPlusCalUnit;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

@RunWith(Parameterized.class)
public class ModularPlusCalParserTest {
	@Parameterized.Parameters
	public static List<Object[]> data() {
		return Arrays.asList(new Object[][]{
				// simple archetype
				{"archetype Archetype() {\n" +
						"  print 1;\n" +
						"}",
						archetype("Archetype",
								Collections.emptyList(),
								Collections.emptyList(),
								Collections.singletonList(printS(num(1))))
				},
		});
	}

	private static final Path testFile = Paths.get("TEST");

	private String unitString;
	private ModularPlusCalUnit unitExpected;

	public ModularPlusCalParserTest(String unitString, ModularPlusCalUnit unitExpected) {
		this.unitString = unitString;
		this.unitExpected = unitExpected;
	}

	@Test
	public void test() throws ParseFailureException {
		LexicalContext ctx = new LexicalContext(testFile, String.join(System.lineSeparator(), unitString.split("\n")));
		System.out.println(unitString);
		ModularPlusCalUnit unit = PlusCalParser.readModularPlusCalUnit(ctx);
		assertThat(unit, is(unitExpected));
	}
}
