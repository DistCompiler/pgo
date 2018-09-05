package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.archetype;
import static pgo.model.mpcal.ModularPlusCalBuilder.mpcalVarDecl;
import static pgo.model.pcal.PlusCalBuilder.*;
import static pgo.model.tla.TLABuilder.*;

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

				// full featured archetype
				{"archetype Archetype(arg1, ref arg2, arg3)\n" +
						"variables local1 = 1, local2 \\in 1..3;\n" +
						"{\n" +
						"  L1: print arg1;\n" +
						"  L2: print arg2;\n" +
						"      print <<arg3, local1, local2>>;\n" +
						"}",
						archetype("Archetype",
								Arrays.asList(
										mpcalVarDecl("arg1", false),
										mpcalVarDecl("arg2", true),
										mpcalVarDecl("arg3", false)),
								Arrays.asList(
										pcalVarDecl("local1", false, num(1)),
										pcalVarDecl("local2", true, binop("..", num(1), num(3)))),
								Arrays.asList(
										labeled(label("L1"), printS(idexp("arg1"))),
										labeled(label("L2"),
												printS(idexp("arg2")),
												printS(tuple(
														idexp("arg3"),
														idexp("local1"),
														idexp("local2"))))))
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
