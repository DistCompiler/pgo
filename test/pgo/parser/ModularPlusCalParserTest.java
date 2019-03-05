package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.mpcal;
import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import pgo.model.mpcal.ModularPlusCalBlock;
import pgo.model.pcal.PlusCalFairness;

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
						"     macro M(a) {\n" +
						"       print a;\n" +
						"     }\n" +
						"     procedure P(b) {\n" +
						"       print b;\n" +
						"     }\n" +
						"     variables global1 = 1, global2 = 2;\n" +
						"     {\n" +
						"       l1: print <<global1, global2>>;\n" +
						"     }\n" +
						"}\n" +
						"*)",
						mpcal("Test",
								Collections.emptyList(), Collections.singletonList(macro("M", Collections.singletonList("a"), printS(idexp("a")))), Collections.singletonList(procedure(
										"P",
										Collections.singletonList(pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
										Collections.emptyList(),
										printS(idexp("b")))), Collections.emptyList(), Collections.emptyList(), Arrays.asList(
										pcalVarDecl("global1", false, false, num(1)),
										pcalVarDecl("global2", false, false, num(2))),
								Collections.emptyList(),
								Collections.singletonList(labeled(
										label("l1"),
										printS(tuple(idexp("global1"), idexp("global2")))
								))
						)
				},
				{"---- MODULE Test ----\n" +
						"(* --mpcal Test {\n" +
						"     macro M(a) {\n" +
						"       print a;\n" +
						"     }\n" +
						"     procedure P(b) {\n" +
						"       print b;\n" +
						"     }\n" +
						"     variables global1 = 1, global2 = 2;\n" +
						"     process (P \\in 1..3) {\n" +
						"       l1: print <<global1, global2>>;\n" +
						"     }\n" +
						"}\n" +
						"*)",
						mpcal("Test",
								Collections.emptyList(),
								Collections.singletonList(macro(
										"M",
										Collections.singletonList("a"),
										printS(idexp("a")))),
								Collections.singletonList(procedure(
										"P",
										Collections.singletonList(pcalVarDecl("b", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
										Collections.emptyList(),
										printS(idexp("b")))), Collections.emptyList(), Collections.emptyList(), Arrays.asList(
										pcalVarDecl("global1", false, false, num(1)),
										pcalVarDecl("global2", false, false, num(2))),
								Collections.emptyList(),
								process(
										pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
										PlusCalFairness.UNFAIR,
										Collections.emptyList(),
										labeled(
												label("l1"),
												printS(tuple(idexp("global1"), idexp("global2")))
										)
								)
						)
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
