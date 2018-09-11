package pgo.parser;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;
import static pgo.model.mpcal.ModularPlusCalBuilder.*;
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
public class ModularPlusCalUnitParserTest {
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
										pcalVarDecl("arg1", false, false, PLUSCAL_DEFAULT_INIT_VALUE),
										pcalVarDecl("arg2", true, false, PLUSCAL_DEFAULT_INIT_VALUE),
										pcalVarDecl("arg3", false, false, PLUSCAL_DEFAULT_INIT_VALUE)),
								Arrays.asList(
										pcalVarDecl("local1", false, false, num(1)),
										pcalVarDecl("local2", false, true, binop("..", num(1), num(3)))),
								Arrays.asList(
										labeled(label("L1"), printS(idexp("arg1"))),
										labeled(label("L2"),
												printS(idexp("arg2")),
												printS(tuple(
														idexp("arg3"),
														idexp("local1"),
														idexp("local2"))))))
				},

				// simple instance
				{"process (P \\in 1..3) = instance Archetype();",
						instance(pcalVarDecl("P", false, true, binop("..", num(1), num(3))),
								"Archetype", Collections.emptyList(), Collections.emptyList())
				},

				// full featured instance
				{"process (P = \"P\") = instance Archetype(ref global1, ref global2, global3)\n" +
						"  mapping global1 via MappingMacro1\n" +
						"  mapping global2 via MappingMacro2;",
						instance(pcalVarDecl("P", false, false, str("P")),
								"Archetype",
								Arrays.asList(
										ref("global1"),
										ref("global2"),
										idexp("global3")),
								Arrays.asList(
										mapping("global1", "MappingMacro1"),
										mapping("global2", "MappingMacro2")))
				},

				// simple mapping macro
				{"mapping macro MappingMacro {\n" +
						"  read {\n" +
						"    yield $value;\n" +
						"  }\n" +
						"  write {\n" +
						"    yield $value;\n" +
						"  }\n" +
						"}",
						mappingMacro("MappingMacro",
								Collections.singletonList(yield(DOLLAR_VALUE)),
								Collections.singletonList(yield(DOLLAR_VALUE)))
				},

				// mapping macro with either
				{"mapping macro UnreliableCounter {\n" +
						"  read {\n" +
						"    yield $value;\n" +
						"  }\n" +
						"  write {\n" +
						"    either {\n" +
						"      yield $variable + $value;\n" +
						"    } or {\n" +
						"      yield $variable;\n" +
						"    }\n" +
						"  }\n" +
						"}",
						mappingMacro("UnreliableCounter",
								Collections.singletonList(yield(DOLLAR_VALUE)),
								Collections.singletonList(
										either(
										Arrays.asList(
												Collections.singletonList(
														yield(binop("+", DOLLAR_VARIABLE, DOLLAR_VALUE))),
												Collections.singletonList(
														yield(DOLLAR_VARIABLE))))))
				},

				// mapping macro with multiple statements
				{"mapping macro MappingMacro {\n" +
						"  read {\n" +
						"    await someSpecialCondition;\n" +
						"    yield $value;\n" +
						"  }\n" +
						"  write {\n" +
						"    yield $value;\n" +
						"  }\n" +
						"}",
						mappingMacro("MappingMacro",
								Arrays.asList(
										await(idexp("someSpecialCondition")),
										yield(DOLLAR_VALUE)),
								Collections.singletonList(yield(DOLLAR_VALUE)))
				}
		});
	}

	private static final Path testFile = Paths.get("TEST");

	private String unitString;
	private ModularPlusCalUnit unitExpected;

	public ModularPlusCalUnitParserTest(String unitString, ModularPlusCalUnit unitExpected) {
		this.unitString = unitString;
		this.unitExpected = unitExpected;
	}

	@Test
	public void test() throws ParseFailureException {
		LexicalContext ctx = new LexicalContext(testFile, String.join(System.lineSeparator(), unitString.split("\n")));
		System.out.println(unitString);
		ModularPlusCalUnit unit = ModularPlusCalParser.readUnit(ctx);
		assertThat(unit, is(unitExpected));
	}
}
