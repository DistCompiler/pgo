package pgo.parser;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

@RunWith(Parameterized.class)
public class PlusCalUnitParserTest {
    @Parameterized.Parameters
    public static List<Object[]> data() {
        return Arrays.asList(new Object[][]{
                // yield in a macro
                {
                    "macro MyMacro() {\n" +
                        "yield x + 1;\n" +
                    "}",
                },

                // yield in a procedure
                {
                        "procedure MyProcedure() {\n" +
                                "either { yield 10 } or { yield 20 };\n" +
                         "}",
                },

                // yield in a process
                {
                        "process MyProcess() {\n" +
                                "while (TRUE) { yield 10 };\n" +
                         "}",
                },

                // special variable in a macro
                {
                        "macro MyMacro() {\n" +
                                "x := $variable + 1;\n" +
                        "}",
                },

                // special variable in a procedure
                {
                        "procedure MyProcedure() {\n" +
                                "either { x := $variable } or { x := $variable + 1 };\n" +
                        "}",
                },

                // special variable in a process
                {
                        "process MyProcess() {\n" +
                                "while (TRUE) { x := $variable };\n" +
                        "}",
                },

                // ref arguments
                {
                        "procedure MyProcedure(ref x) {\n" +
                                "either { x := 10 } or { x := 20 };\n" +
                        "}",
                },
        });
    }

    private static final Path testFile = Paths.get("TEST");

    private String unit;

    public PlusCalUnitParserTest(String unit) {
        this.unit = unit;
    }

    @Test(expected = ParseFailureException.class)
    public void test() throws ParseFailureException {
        LexicalContext ctx = new LexicalContext(testFile, String.join(System.lineSeparator(), unit.split("\n")));
        System.out.println(unit);

        PlusCalParser.readUnit(ctx);
    }
}